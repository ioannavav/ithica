#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/IRBuilder.h"
#include <vector>
#include <map>
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Support/ErrorHandling.h"


using namespace llvm;
static std::map<unsigned, Function*> NoOpFunctionRegistry;


namespace {
	struct ArithMemDivPass : public FunctionPass {
		static char ID;
		ArithMemDivPass() : FunctionPass(ID) {}


		static unsigned blockCounter; // Basic block ID of the function
		static unsigned totalBasicBlocks; //Total number of basic blocks across functions
		static bool countedBlocks; // Ensure basic blocks are counted only once    
		
		bool isExcludedInstruction(Instruction *inst) {

			if (isa<InsertElementInst>(inst) || isa<AllocaInst>(inst) ||
					isa<AtomicCmpXchgInst>(inst) || (isa<LandingPadInst>(inst)) || 
					isa<InsertValueInst>(inst)|| isa<FenceInst>(inst) || isa<PHINode>(inst) || 
					isa<AtomicRMWInst>(inst)) {
				return true;
			}
            
			if (isa<LoadInst>(inst)) {
				// Don't duplicate atomic loads
				if (dyn_cast<LoadInst>(inst)->isAtomic()) {
					return true;
				}
				// Don't duplicate volatile loads
				if (dyn_cast<LoadInst>(inst)->isVolatile()) {
					return true;
				}
			}

			if (isa<StoreInst>(inst)) {
				if (dyn_cast<StoreInst>(inst)->isAtomic()) {
					return true;
				}
				if (dyn_cast<StoreInst>(inst)->isVolatile()) {
					return true;
				}
			}

			if (auto *callInst = dyn_cast<CallInst>(inst)) {

				//Exclude calls with sideffects
				if (callInst->mayHaveSideEffects()) {
					return true;
				}

				if (callInst->isInlineAsm()) {
					InlineAsm *inlineAsm = dyn_cast<InlineAsm>(callInst->getCalledOperand());
					// Exclude inline assembly system calls
					if (inlineAsm && inlineAsm->getAsmString().find("syscall") != std::string::npos) {
						return true; 
					}
					// Include all other inline assembly calls
					return false;
				}
				
				if (auto *callInst = dyn_cast<CallInst>(inst)) {
					if (Function *calledFunction = callInst->getCalledFunction()) {
						if (calledFunction->getName().contains("llvm.") && !callInst->getType()->isVoidTy()) {
							// Check if the called function has the `readonly` or `readnone` attribute. If yes, include it
							if (calledFunction->hasFnAttribute(Attribute::ReadOnly) || calledFunction->hasFnAttribute(Attribute::ReadNone)) {
								return false;
							}
						}
					}
				}

				// Don't duplicate void calls (they do not return a value to compare)
				if (callInst->getType()->isVoidTy()) {
					return true;
				}
				
				return true;
			}

			return false;
		}


		std::string instructionToString(Instruction *I) {
			if (!I) {
				return "<null instruction>";
			}

			std::string str;
			raw_string_ostream rso(str);

			I->print(rso);
			rso.flush();

			std::string safeStr;
			for (char c : rso.str()) {
				if (c == '%') {
					safeStr += "%_"; 
				} else {
					safeStr += c;
				}
			}
			return safeStr;
		}


		//Exclude Then/Else blocks from getting duplicated. These are blocks that the instrumentation adds
		bool isThenElseBlock(BasicBlock &BB) {
			StringRef name = BB.getName();
			return name.startswith("then") || name.startswith("else");
		}


		bool containsResumeOrCleanupInstruction(BasicBlock &BB) {
			for (Instruction &I : BB) {
				if ((isa<ResumeInst>(&I))||(isa<LandingPadInst>(&I))) {
					return true;
				}
			}
			return false;
		}


		// Function to handle operands with the volatile load/store trick
		Value* handleOperand(Value *operand, Function &func, IRBuilder<> &builder, IRBuilder<> &allocaBuilder) {
			if (isa<Constant>(operand)) {
				// If operand is a constant, return it directly without volatile handling
				//errs() << "Skipping volatile handling for constant operand: " << *operand << "\n";
				return operand;
			}
			if (isa<GetElementPtrInst>(operand)) {
				return operand;
			}

			// By putting all the allocas at the beginning of the first basic block of the function (=static allocas), they get run in the prolog/epilog of the function and therefore they are basically free. Without this trick we would run into stack overflow very easily 
			BasicBlock &entryBlock = func.getEntryBlock();
			allocaBuilder.SetInsertPoint(&entryBlock, entryBlock.getFirstInsertionPt()); // Set the insertion point of the alloca to the beginning of the entry block

			AllocaInst *alloca = allocaBuilder.CreateAlloca(operand->getType(), nullptr, "volatile_alloca");

			// Determine the correct alignment, if it exists
			if (auto *oper_loadInst = dyn_cast<LoadInst>(operand)) {
				alloca->setAlignment(oper_loadInst->getAlign());
			} else if (auto *oper_storeInst = dyn_cast<StoreInst>(operand)) {
				alloca->setAlignment(oper_storeInst->getAlign());
			} 

			StoreInst *storeInst = builder.CreateStore(operand, alloca);
			storeInst->setVolatile(true);
			storeInst->setAlignment(alloca->getAlign());
			LoadInst *loadInst = builder.CreateLoad(alloca->getAllocatedType(), alloca);
			loadInst->setVolatile(true);
			loadInst->setAlignment(alloca->getAlign());
			// The instruction that contains the new version of the argument is the volatile load instruction
			return loadInst;
		}


		bool isExcludedFunction(Function *F) {
			static const std::set<std::string> ExcludedFunctions = {
				"Function_name_to_exclude"
			};
			for (const auto &excludedName : ExcludedFunctions) {
				if (F->getName().str().find(excludedName) != std::string::npos) {
					return true;
				}
			}
			return false;
		}



		bool runOnFunction(Function &F) override {

			int blockSize = 
			#ifdef BLOCKSIZE
				BLOCKSIZE;
			#else
				1; 
			#endif
		
			int interleaving = 
			#ifdef INTERLEAVING
				INTERLEAVING;
			#else
				1; 
			#endif
		
			const char* libraryName = 
			#ifdef LIBRARYNAME
				LIBRARYNAME;
			#else
				"top-level code"; 
			#endif

			if (isExcludedFunction(&F)) {
				return false;
			}

			LLVMContext &Ctx = F.getContext();

			// Use fprintf to print in the stderr (unbuffered)
			FunctionCallee fprintFunc = F.getParent()->getOrInsertFunction(
					"fprintFunc", FunctionType::get(IntegerType::getInt32Ty(Ctx),
						PointerType::get(Type::getInt8Ty(Ctx), 0)));

			FunctionCallee printCPUFunc = F.getParent()->getOrInsertFunction("print_cpu_id",
					FunctionType::get(Type::getVoidTy(Ctx), false));

			FunctionCallee printDateFunc = F.getParent()->getOrInsertFunction("print_date",
					llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), llvm::Type::getInt8PtrTy(Ctx), false)
			);

			if (!countedBlocks) {
				// Count basic blocks on the first invocation
				countBasicBlocks(F.getParent());
				countedBlocks = true;
			}

			// Keep the original basic blocks in a separate structure to keep them unchanged.
			// This is needed because we are adding new basic blocks on the go
			std::vector<BasicBlock*> bbs;
			for (Function::iterator BI = F.begin(), BE = F.end(); BI != BE; ++BI) {
				BasicBlock *BB = &*BI;
				bbs.push_back(BB);
			}


			for (auto BI : bbs) {
				BasicBlock *BB = &*BI;

				if (isThenElseBlock(*BB)) {
					// There shouldn't be any then/else blocks here but double checking
					continue;

				}

				if (containsResumeOrCleanupInstruction(*BB)) {
					continue;
				}

				std::vector<Instruction*> originalInstructions;
				std::vector<Value*> originalValues; //for stores
				std::map<Instruction*, std::vector<Instruction*>> dependencyGraph;


				for (Instruction &I : *BB) {
					if (&I != BB->getTerminator() && !isExcludedInstruction(&I)) {
						originalInstructions.push_back(&I);
						originalValues.push_back(&I);


						// Construct the dependency graph
						std::vector<Instruction*> dependencies;
						for (Use &U : I.operands()) {
							if (Instruction *depInst = dyn_cast<Instruction>(U.get())) {
								dependencies.push_back(depInst);
							}
						}
						dependencyGraph[&I] = dependencies;
					}
				}

				// Identify independent clusters
				std::vector<Instruction*> independentClusters;
				for (auto &entry : dependencyGraph) {
					Instruction *inst = entry.first;
					std::vector<Instruction*> &deps = entry.second;

					bool isEndOfCluster = true;
					for (auto &pair : dependencyGraph) {
						if (std::find(pair.second.begin(), pair.second.end(), inst) != pair.second.end()) {
							isEndOfCluster = false;
							break;
						}
					}
					if (isEndOfCluster) {
						independentClusters.push_back(inst);
					}
				}

				std::map<Instruction*, std::vector<Instruction*>> cloneMap;
				std::map<Instruction*, Value*> InstToValueMap; //for stores
				std::vector<std::pair<Value*, Instruction*>> icmpResults;  // Pair of cmp result and instruction string

				Instruction *lastInst = nullptr;  // Declare lastInst outside the loop
				Instruction *clonedLastInst = nullptr;  // Declare clonedLastInst outside the loop



				// ALLOCAS
				// Create an IRBuilder for allocas at the beginning of the basic block.
				// This is passed as argument to the handleOperands function
				IRBuilder<> allocaBuilder(BB);
				allocaBuilder.SetInsertPoint(BB->getFirstNonPHI());

				unsigned instCounter = 0;

				// Loop through each instruction of the basic block
		for (Instruction *Inst : originalInstructions) {
			instCounter++;

			IRBuilder<> builder(Inst);
			std::vector<Value*> clonedOperands;
			std::vector<Value*> dependencyOperands;

			Instruction *clonedInst = nullptr;
			std::vector<Instruction*> clonedInsts; //memdiv

			//Handle Stores
			if (isa<StoreInst>(Inst)) {
				IRBuilder<> storeBuilder(BB);	
				storeBuilder.SetInsertPoint(Inst->getNextNode());
				Value *storedValue = Inst->getOperand(0);
				Value *storeAddress = Inst->getOperand(1);

				//Corner Cases
				// Check if storeAddress is a valid pointer type
				if (!storeAddress->getType()->isPointerTy()) {
					errs() << "Store address is not a pointer type: " << *storeAddress << "\n";
					continue;
				}
				// Ensure the store address is not a constant null pointer
				if (isa<ConstantPointerNull>(storeAddress)) {
					errs() << "Store address is a constant null pointer: " << *storeAddress << "\n";
					continue;
				}
				// Ensure the pointer's element type matches the stored value's type
				Type *storedType = storeAddress->getType()->getPointerElementType();
				if (storedType != storedValue->getType()) {
					errs() << "Pointer element type does not match stored value type: "
					<< *storedType << " vs " << *storedValue->getType() << "\n";
					continue;
				}

		
				LoadInst *reloadedValue = storeBuilder.CreateLoad(storeAddress->getType()->getPointerElementType(), storeAddress, true); 
				reloadedValue->setAlignment(dyn_cast<StoreInst>(Inst)->getAlign());
				clonedInst = reloadedValue;
				originalValues[instCounter-1] = storedValue;
				InstToValueMap[Inst] = storedValue;					

				// Memory Diversity for Stores
				IRBuilder<> fenceBuilder(BB);
				fenceBuilder.SetInsertPoint(reloadedValue->getNextNode());
				InlineAsm *mfenceAsm = InlineAsm::get(FunctionType::get(Type::getVoidTy(F.getContext()), false), "mfence", "", true);
				fenceBuilder.CreateCall(mfenceAsm);

				// Insert another volatile load after the mfence
				LoadInst *reloadedValue2 = fenceBuilder.CreateLoad(storeAddress->getType()->getPointerElementType(), storeAddress, true);
				reloadedValue2->setAlignment(dyn_cast<StoreInst>(Inst)->getAlign());
				reloadedValue2->setVolatile(true);

				// Insert clflush after the second volatile load
				IRBuilder<> clflushBuilder(BB);
				clflushBuilder.SetInsertPoint(reloadedValue2->getNextNode());
				InlineAsm *clflushAsm = InlineAsm::get(FunctionType::get(Type::getVoidTy(F.getContext()), storeAddress->getType(), false), "clflush $0", "m", true);
				clflushBuilder.CreateCall(clflushAsm, storeAddress);

				// Insert another volatile load after clflush
				LoadInst *reloadedValue3 = clflushBuilder.CreateLoad(storeAddress->getType()->getPointerElementType(), storeAddress, true);
				reloadedValue3->setAlignment(dyn_cast<StoreInst>(Inst)->getAlign());
				reloadedValue3->setVolatile(true);	

				//Insert 3 pairs of instructions to be compaired
				clonedInsts.push_back(reloadedValue);
				clonedInsts.push_back(reloadedValue2);
				clonedInsts.push_back(reloadedValue3);	
			
			} else {
				clonedInst = Inst->clone();

				if (isa<LoadInst>(Inst)) {
					LoadInst *loadInst = dyn_cast<LoadInst>(Inst);
					LoadInst *clonedLoadInst = dyn_cast<LoadInst>(clonedInst);
					clonedLoadInst->setAlignment(loadInst->getAlign());
					clonedInst = clonedLoadInst;
				} 
			
				if (!(isa<CallInst>(Inst)) || 
						(isa<CallInst>(Inst) && cast<CallInst>(Inst)->getCalledFunction() && 
						(cast<CallInst>(Inst)->getCalledFunction()->getName().contains("bzhi") ||
						cast<CallInst>(Inst)->getCalledFunction()->getName().contains("movsb") ||
						cast<CallInst>(Inst)->getCalledFunction()->getName().contains("stosb")) )) { 


					// Maintain dependencies
					for (unsigned i = 0; i < Inst->getNumOperands(); ++i) {
						Value *operand = Inst->getOperand(i);
						if (cloneMap.find(dyn_cast<Instruction>(operand)) != cloneMap.end()) {
							// If there's a duplicate instruction for the operand, use that
							auto &clonedInsts = cloneMap[dyn_cast<Instruction>(operand)];
							if (!clonedInsts.empty()) {
								// Push the first cloned instruction into dependencyOperands
								dependencyOperands.push_back(clonedInsts[0]);
							} 
						} else {
							dependencyOperands.push_back(operand);
						}
					}
					for (size_t j = 0; j < dependencyOperands.size(); ++j) {
							clonedInst->setOperand(j, dependencyOperands[j]);
					}

					
					//Volatile
					bool atleastonehandled = false;
					for (unsigned i = 0; i < clonedInst->getNumOperands(); ++i) {
						Value *operand = clonedInst->getOperand(i);
						if (isa<Constant>(operand)) {
							// If operand is a constant, don't do volatile handling
							clonedOperands.push_back(operand);
						} else {
							atleastonehandled = true;
							Value *volatileOperand = handleOperand(operand, F, builder, allocaBuilder);
							clonedOperands.push_back(volatileOperand); 
						}
					}
					if (LoadInst *clonedLoad = dyn_cast<LoadInst>(clonedInst)) {
						clonedLoad->setVolatile(true);
					}
					if (atleastonehandled == false) {
						if (isa<LoadInst>(Inst)) {
							if (LoadInst *clonedLoad = dyn_cast<LoadInst>(clonedInst)) {
								clonedLoad->setVolatile(true);
							} else {
								errs() << "Shouldn't be here." << *Inst << "\n";
							}
						} else {
								errs() << "Corner case to handle: " << *Inst << " with argument: " << *(Inst->getOperand(0))  << "\n";
						}
					}
					
				}

				for (size_t j = 0; j < clonedOperands.size(); ++j) {
					clonedInst->setOperand(j, clonedOperands[j]);
				}

				if (interleaving == 1 || isa<LoadInst>(Inst)) {
					clonedInst->insertAfter(Inst);
				} else if (interleaving == 0) {
					clonedInst->insertBefore(BB->getTerminator());
				}


				//Memory diversity for loads: Clflush between loads
				if (isa<LoadInst>(Inst)) {
					IRBuilder<> clflushBuilder(BB);
					clflushBuilder.SetInsertPoint(Inst->getNextNode());
					auto *loadInst = dyn_cast<LoadInst>(Inst);
					Value *loadPtr = loadInst->getPointerOperand();
					Type *PtrType = loadPtr->getType();
					Type *VoidTy = Type::getVoidTy(F.getContext());
					InlineAsm *clflushAsm = InlineAsm::get(FunctionType::get(VoidTy, PtrType, false), "clflush $0", "m", true);
					CallInst *clflushCall = clflushBuilder.CreateCall(clflushAsm, loadPtr);
				}
				clonedInsts.push_back(clonedInst);

			}
			

			if (!clonedInsts.empty()) {
				for (size_t ci = 0; ci < clonedInsts.size(); ++ci) {

					cloneMap[Inst].push_back(clonedInsts[ci]);
					clonedLastInst = clonedInsts[ci];

					Value *lastValue = nullptr;
					Instruction *lastInst = originalInstructions[instCounter - 1];

					if (isa<StoreInst>(Inst)) {
						lastValue = originalValues[instCounter - 1];
					} 

					
                    if ((blockSize == 0 && (std::find(independentClusters.begin(), independentClusters.end(), lastInst) != independentClusters.end()))
					|| (blockSize !=0 && (instCounter % blockSize == 0 || instCounter == originalInstructions.size()))) {

						
						if (cloneMap.find(lastInst) == cloneMap.end()) {
								errs() << "Error: No instruction in cloneMap." << "\n";
						} else {
								Instruction *clonedLastInst = cloneMap[lastInst][0];
						}

						IRBuilder<> builder(BB->getTerminator());
						Value *cmp = nullptr;

						//Comparisons
                        if (lastValue) {
                            if (lastValue->getType()->isIntegerTy() && clonedLastInst->getType()->isIntegerTy()) {
                                cmp = builder.CreateICmpEQ(lastValue, clonedLastInst, "cmp_result" + std::to_string(blockCounter));
                            } else if (lastValue->getType()->isFloatingPointTy() && clonedLastInst->getType()->isFloatingPointTy()) {
                                cmp = builder.CreateFCmpOEQ(lastValue, clonedLastInst, "cmp_result" + std::to_string(blockCounter));
                            } else if (isa<VectorType>(lastValue->getType())) {
                                auto *vecType = cast<VectorType>(lastValue->getType());
                                Value *vectorCmp = ConstantInt::getTrue(builder.getContext());
                                unsigned numElements = vecType->getElementCount().getKnownMinValue(); 
                                for (unsigned i = 0; i < numElements; ++i) {
                                    Value *elem1 = builder.CreateExtractElement(lastValue, ConstantInt::get(Type::getInt32Ty(builder.getContext()), i), "vec_elem1");
                                    Value *elem2 = builder.CreateExtractElement(clonedLastInst, ConstantInt::get(Type::getInt32Ty(builder.getContext()), i), "vec_elem2");
                                    Value *elemCmp = nullptr;
                                    if (vecType->getElementType()->isIntegerTy()) {
                                        elemCmp = builder.CreateICmpEQ(elem1, elem2);
                                    } else if (vecType->getElementType()->isFloatingPointTy()) {
                                        elemCmp = builder.CreateFCmpOEQ(elem1, elem2);
                                    } else if (vecType->getElementType()->isPointerTy()) {
                                        auto *intType = builder.getIntPtrTy(clonedLastInst->getModule()->getDataLayout());
                                        Value *intVal1 = builder.CreatePtrToInt(elem1, intType, "ptr_to_int1");
                                        Value *intVal2 = builder.CreatePtrToInt(elem2, intType, "ptr_to_int2");
                                        elemCmp = builder.CreateICmpEQ(intVal1, intVal2, "ptr_cmp_result");

                                    } else {
                                        errs() << "Unsupported vector element type for comparison for: " << *lastInst<< " with type: ";
                                        lastValue->getType()->print(errs());
                                        errs() << "\n";
                                        vectorCmp = nullptr;
                                        break;
                                    }
                                    vectorCmp = builder.CreateAnd(vectorCmp, elemCmp, "vec_cmp_agg");
                                }
                                cmp = vectorCmp;
                                if (cmp == nullptr) {
                                    errs() << "Vector comparison failed." << *(Inst) << "\n";
                                }
                            
                            // Pointers
                            } else if (lastValue->getType()->isPointerTy() || clonedLastInst->getType()->isPointerTy()) {
                                // Convert pointers to integer type before comparison
                                auto *intType = builder.getIntPtrTy(clonedLastInst->getModule()->getDataLayout());
                                Value *intVal1 = builder.CreatePtrToInt(lastValue, intType, "ptr_to_int1");
                                Value *intVal2 = builder.CreatePtrToInt(clonedLastInst, intType, "ptr_to_int2");
                                cmp = builder.CreateICmpEQ(intVal1, intVal2, "ptr_cmp_result");
                                //}	
                            } else if (isa<StructType>(lastValue->getType())) {
                                errs() << "STRUCT: " << *lastValue << "\n";
                                auto *structType = cast<StructType>(lastValue->getType());
                                Value *structCmp = ConstantInt::getTrue(builder.getContext());
                                unsigned numElements = structType->getNumElements();
                                for (unsigned i = 0; i < numElements; ++i) {
                                    Value *elem1 = builder.CreateExtractValue(lastValue, i, "struct_elem1");
                                    Value *elem2 = builder.CreateExtractValue(clonedLastInst, i, "struct_elem2");
                                    Value *elemCmp = nullptr;
                                    if (structType->getElementType(i)->isIntegerTy()) {
                                        elemCmp = builder.CreateICmpEQ(elem1, elem2);
                                    } else if (structType->getElementType(i)->isFloatingPointTy()) {
                                        elemCmp = builder.CreateFCmpOEQ(elem1, elem2);
                                    } else if (structType->getElementType(i)->isPointerTy()) {
                                    }  else if (isa<StructType>(lastValue->getType())) {
                                        auto *structType = cast<StructType>(lastValue->getType());
                                        Value *structCmp = ConstantInt::getTrue(builder.getContext());
                                        unsigned numElements = structType->getNumElements();
                                        for (unsigned i = 0; i < numElements; ++i) {
                                            Value *elem1 = builder.CreateExtractValue(lastValue, i, "struct_elem1");
                                            Value *elem2 = builder.CreateExtractValue(clonedLastInst, i, "struct_elem2");
                                            Value *elemCmp = nullptr;
                                            if (structType->getElementType(i)->isIntegerTy()) {
                                                elemCmp = builder.CreateICmpEQ(elem1, elem2);
                                            } else if (structType->getElementType(i)->isFloatingPointTy()) {
                                                elemCmp = builder.CreateFCmpOEQ(elem1, elem2);
                                            } else if (structType->getElementType(i)->isPointerTy()) {
                                                auto *intType = builder.getIntPtrTy(clonedLastInst->getModule()->getDataLayout());
                                                Value *intVal1 = builder.CreatePtrToInt(elem1, intType, "ptr_to_int1");
                                                Value *intVal2 = builder.CreatePtrToInt(elem2, intType, "ptr_to_int2");
                                                elemCmp = builder.CreateICmpEQ(intVal1, intVal2, "ptr_cmp_result");
                                            } else {
                                                errs() << "Unsupported struct element type for comparison.\n";
                                                structCmp = nullptr;
                                                break;
                                            }
                                            structCmp = builder.CreateAnd(structCmp, elemCmp, "struct_cmp_agg");
                                        }
                                        cmp = structCmp;
                                        if (cmp == nullptr) {
                                            errs() << "Struct comparison failed." << *(Inst) << "\n";
                                        }
                                    }
                                }


                            }  else {
                                lastValue->getType()->print(errs());
                                errs() << "\n";
                            }
                        } else {
                            if (lastInst->getType()->isIntegerTy() && clonedLastInst->getType()->isIntegerTy()) {
                                cmp = builder.CreateICmpEQ(lastInst, clonedLastInst, "cmp_result" + std::to_string(blockCounter));
                            } else if (lastInst->getType()->isFloatingPointTy() && clonedLastInst->getType()->isFloatingPointTy()) {
                                cmp = builder.CreateFCmpOEQ(lastInst, clonedLastInst, "cmp_result" + std::to_string(blockCounter));
                            } else if (isa<VectorType>(lastInst->getType())) {
                                auto *vecType = cast<VectorType>(lastInst->getType());
                                Value *vectorCmp = ConstantInt::getTrue(builder.getContext());
                                unsigned numElements = vecType->getElementCount().getKnownMinValue(); 
                                for (unsigned i = 0; i < numElements; ++i) {
                                    Value *elem1 = builder.CreateExtractElement(lastInst, ConstantInt::get(Type::getInt32Ty(builder.getContext()), i), "vec_elem1");
                                    Value *elem2 = builder.CreateExtractElement(clonedLastInst, ConstantInt::get(Type::getInt32Ty(builder.getContext()), i), "vec_elem2");
                                    Value *elemCmp = nullptr;
                                    if (vecType->getElementType()->isIntegerTy()) {
                                        elemCmp = builder.CreateICmpEQ(elem1, elem2);
                                    } else if (vecType->getElementType()->isFloatingPointTy()) {
                                        elemCmp = builder.CreateFCmpOEQ(elem1, elem2);
                                    } else if (vecType->getElementType()->isPointerTy()) {
                                        auto *intType = builder.getIntPtrTy(clonedLastInst->getModule()->getDataLayout());
                                        Value *intVal1 = builder.CreatePtrToInt(elem1, intType, "ptr_to_int1");
                                        Value *intVal2 = builder.CreatePtrToInt(elem2, intType, "ptr_to_int2");
                                        elemCmp = builder.CreateICmpEQ(intVal1, intVal2, "ptr_cmp_result");

                                    } else {
                                        errs() << "!!! Unsupported vector element type for comparison for: " << *lastInst<< " with type: ";
                                        lastInst->getType()->print(errs());
                                        errs() << "\n";
                                        vectorCmp = nullptr;
                                        break;
                                    }
                                    vectorCmp = builder.CreateAnd(vectorCmp, elemCmp, "vec_cmp_agg");
                                }
                                cmp = vectorCmp;
                                if (cmp == nullptr) {
                                    errs() << "!!!!!!!!!! VECTOR_COMPARISON FAILED: FIX IT " << *(Inst) << "\n";
                                }
                            
                            // Pointers
                            } else if (lastInst->getType()->isPointerTy() || clonedLastInst->getType()->isPointerTy()) {
                                // Convert pointers to integer type before comparison
                                auto *intType = builder.getIntPtrTy(clonedLastInst->getModule()->getDataLayout());
                                Value *intVal1 = builder.CreatePtrToInt(lastInst, intType, "ptr_to_int1");
                                Value *intVal2 = builder.CreatePtrToInt(clonedLastInst, intType, "ptr_to_int2");
                                cmp = builder.CreateICmpEQ(intVal1, intVal2, "ptr_cmp_result");
                                //}	
                            } else if (isa<StructType>(lastInst->getType())) {
                                errs() << "STRUCT: " << *lastInst << "\n";
                                auto *structType = cast<StructType>(lastInst->getType());
                                Value *structCmp = ConstantInt::getTrue(builder.getContext());
                                unsigned numElements = structType->getNumElements();
                                for (unsigned i = 0; i < numElements; ++i) {
                                    Value *elem1 = builder.CreateExtractValue(lastInst, i, "struct_elem1");
                                    Value *elem2 = builder.CreateExtractValue(clonedLastInst, i, "struct_elem2");
                                    Value *elemCmp = nullptr;
                                    if (structType->getElementType(i)->isIntegerTy()) {
                                        elemCmp = builder.CreateICmpEQ(elem1, elem2);
                                    } else if (structType->getElementType(i)->isFloatingPointTy()) {
                                        elemCmp = builder.CreateFCmpOEQ(elem1, elem2);
                                    } else if (structType->getElementType(i)->isPointerTy()) {
                                    }  else if (isa<StructType>(lastInst->getType())) {
                                        auto *structType = cast<StructType>(lastInst->getType());
                                        Value *structCmp = ConstantInt::getTrue(builder.getContext());
                                        unsigned numElements = structType->getNumElements();
                                        for (unsigned i = 0; i < numElements; ++i) {
                                            Value *elem1 = builder.CreateExtractValue(lastInst, i, "struct_elem1");
                                            Value *elem2 = builder.CreateExtractValue(clonedLastInst, i, "struct_elem2");
                                            Value *elemCmp = nullptr;
                                            if (structType->getElementType(i)->isIntegerTy()) {
                                                elemCmp = builder.CreateICmpEQ(elem1, elem2);
                                            } else if (structType->getElementType(i)->isFloatingPointTy()) {
                                                elemCmp = builder.CreateFCmpOEQ(elem1, elem2);
                                            } else if (structType->getElementType(i)->isPointerTy()) {
                                                auto *intType = builder.getIntPtrTy(clonedLastInst->getModule()->getDataLayout());
                                                Value *intVal1 = builder.CreatePtrToInt(elem1, intType, "ptr_to_int1");
                                                Value *intVal2 = builder.CreatePtrToInt(elem2, intType, "ptr_to_int2");
                                                elemCmp = builder.CreateICmpEQ(intVal1, intVal2, "ptr_cmp_result");
                                            } else {
                                                errs() << "Unsupported struct element type for comparison.\n";
                                                structCmp = nullptr;
                                                break;
                                            }
                                            structCmp = builder.CreateAnd(structCmp, elemCmp, "struct_cmp_agg");
                                        }
                                        cmp = structCmp;
                                        if (cmp == nullptr) {
                                            errs() << "Struct comparison failed." << *(Inst) << "\n";
                                        }
                                    }
                                }


                            }  else {
                                errs() << "No comparison supported yet for instruction (shouldn't be here)." << *Inst << " is of type: ";
                                lastInst->getType()->print(errs());
                                errs() << "\n";
                            }
                        }

						if (cmp) {
							icmpResults.push_back(std::make_pair(cmp, lastInst));
						}
					}	
				}
			}
		}

		// Create the comparison by aggregating the results of all icmp instructions
		// And create the corresponding then/else blocks
		if (!icmpResults.empty()) {
			IRBuilder<> aggCmpBuilder(BB->getTerminator());
			Value *aggregateCmp = nullptr;

			if (icmpResults.size() == 1) {
				aggregateCmp = icmpResults[0].first;
			} else {
				aggregateCmp = aggCmpBuilder.CreateAnd(icmpResults[0].first, icmpResults[1].first, "init_agg_cmp");
				for (unsigned i = 2; i < icmpResults.size(); ++i) {
					aggregateCmp = aggCmpBuilder.CreateAnd(aggregateCmp, icmpResults[i].first, "agg_cmp");
				}
			}

		
			BasicBlock *thenBB = BB->splitBasicBlock(aggCmpBuilder.GetInsertPoint(), "then" + std::to_string(blockCounter));
			BasicBlock *elseBB = BasicBlock::Create(Ctx, "else" + std::to_string(blockCounter), &F, thenBB);


			BB->getTerminator()->eraseFromParent();
			aggCmpBuilder.SetInsertPoint(BB);
			aggCmpBuilder.CreateCondBr(aggregateCmp, thenBB, elseBB);


			IRBuilder<> elseBuilder(elseBB);

			// Call print_cpu_id function on mismatch
			elseBuilder.CreateCall(printCPUFunc);
			llvm::Value* libraryNameArg = elseBuilder.CreateGlobalStringPtr(libraryName);
			elseBuilder.CreateCall(printDateFunc, libraryNameArg);

			Value* funcName = elseBuilder.CreateGlobalStringPtr(F.getName());
			Value* blockIdValue = ConstantInt::get(Type::getInt32Ty(Ctx), blockCounter);
			Value * functionStr = elseBuilder.CreateGlobalStringPtr("Error in function: %s , #Basic block: %d \n \0");
			elseBuilder.CreateCall(fprintFunc, {functionStr, funcName, blockIdValue});



			for (auto &icmpPair : icmpResults) {
				Instruction * origInstr = icmpPair.second;
				Value *origValue = nullptr;
				if (isa<StoreInst>(origInstr)) {
					origValue = InstToValueMap[origInstr];
				}
				
				std::string origInstrStr = instructionToString(origInstr);
				Value *instName = elseBuilder.CreateGlobalStringPtr(origInstrStr.c_str());
				auto clonedInstrItr = cloneMap.find(origInstr);
				if (clonedInstrItr == cloneMap.end()) {
					errs() << "Error: No instruction in cloneMap!" << "\n";
				}

				Instruction * clonedInstr = cloneMap[origInstr][0];
				if (origValue) {
					Type * instReturnType1 = origValue->getType();
				} else {
					Type * instReturnType1 = origInstr->getType();
				}
				
				Type * instReturnType2 = clonedInstr->getType();

				Value * formatStr = elseBuilder.CreateGlobalStringPtr("Potential Failing Instruction: %s \n");
				Value * newLine = elseBuilder.CreateGlobalStringPtr("\n");

				Value *Zero = elseBuilder.getInt8(0);

				//Since the allocation of space for the printing is happening at compile time, it could be the case that this changes at runtime after the optimizations are performed. 
				// For this reason, we allocate a big enough constant amount of space (64 bytes) for all instructions. Probably unecessary.
				Value *SizeVal = elseBuilder.getInt32(64); // 64 bytes
				MaybeAlign Alignment(8); // Assume alignment of 1, adjust as needed
				Value *IsVolatile = elseBuilder.getInt1(true); // Volatile

				// Create an array type of 64 elements, each of type i8 (1 byte)
				ArrayType* Int64ArrayType = ArrayType::get(Zero->getType(), 64);

				AllocaInst* allocaInstr1 = elseBuilder.CreateAlloca(Int64ArrayType, nullptr, "alloca1");
				AllocaInst* allocaInstr2 = elseBuilder.CreateAlloca(Int64ArrayType, nullptr, "alloca2");


				elseBuilder.CreateMemSet(allocaInstr1, Zero, SizeVal, Alignment, true);
				elseBuilder.CreateMemSet(allocaInstr2, Zero, SizeVal, Alignment, true);

				// Create store instructions in the else block
				PointerType *origin_ptr = nullptr;
				if (origValue) {
					origin_ptr = PointerType::getUnqual(origValue->getType());
				} else {
					origin_ptr = PointerType::getUnqual(origInstr->getType());
				}
				PointerType *cloned_ptr = PointerType::getUnqual(clonedInstr->getType());

				Value *castedPtr1 = elseBuilder.CreateBitCast(allocaInstr1, origin_ptr);
				Value *castedPtr2 = elseBuilder.CreateBitCast(allocaInstr2, cloned_ptr);
				
				StoreInst* storeInstr1 = nullptr;
				if (origValue) {
					storeInstr1 = elseBuilder.CreateStore(origValue, castedPtr1, true);
				} else {
					storeInstr1 = elseBuilder.CreateStore(origInstr, castedPtr1, true);
				}
				StoreInst* storeInstr2 = elseBuilder.CreateStore(clonedInstr, castedPtr2, true);

				TypeSize size1 = F.getParent()->getDataLayout().getTypeStoreSize(allocaInstr1->getAllocatedType());
				TypeSize size2 = F.getParent()->getDataLayout().getTypeStoreSize(allocaInstr2->getAllocatedType());

				Value * addr1 = storeInstr1->getOperand(1);
				Value * addr2 = storeInstr2->getOperand(1);

				Value * castedAddr1 = elseBuilder.CreatePointerCast(addr1, Type::getInt8PtrTy(Ctx), "pointerCast");
				Value * castedAddr2 = elseBuilder.CreatePointerCast(addr2, Type::getInt8PtrTy(Ctx), "pointerCast");

				FunctionCallee pp = F.getParent()->getOrInsertFunction("printMemoryAsHex", Type::getInt32PtrTy(Ctx), Type::getInt8PtrTy(Ctx), Type::getInt32Ty(Ctx), Type::getInt8PtrTy(Ctx), Type::getInt32Ty(Ctx));

				// Incr_err helps us set a limit to the amount of errors we want to print. Currently disabled
				////FunctionCallee incr_err = F.getParent()->getOrInsertFunction("incr_err", Type::getInt32PtrTy(Ctx), Type::getInt32Ty(Ctx), Type::getInt32Ty(Ctx));


				Value * size_bytes1 = ConstantInt::get(Type::getInt32Ty(Ctx), size1, false);
				Value * size_bytes2 = ConstantInt::get(Type::getInt32Ty(Ctx), size2, false);

				Value * bb_index = ConstantInt::get(Type::getInt32Ty(Ctx), blockCounter, false);
				Value * bb_total = ConstantInt::get(Type::getInt32Ty(Ctx), totalBasicBlocks, false);

				////elseBuilder.CreateCall(incr_err, {bb_index, bb_total});
				elseBuilder.CreateCall(fprintFunc, {formatStr, instName});
				elseBuilder.CreateCall(pp, {castedAddr1, size_bytes1, castedAddr2, size_bytes2});
				elseBuilder.CreateCall(fprintFunc, {newLine});
				///}
			}

			// This will increase build time significantly. You can remove for quick building (less logging)
			std::string separator1 = "-------------- Beginning Of Failing Block ------------\n";
			Value *separatorStrVal1 = elseBuilder.CreateGlobalStringPtr(separator1.c_str());
			elseBuilder.CreateCall(fprintFunc, {separatorStrVal1});
			for (Instruction &I : *BB) {
				std::string instructionStr = instructionToString(&I) + "\n";
				Value *instructionStrVal = elseBuilder.CreateGlobalStringPtr(instructionStr.c_str());
				elseBuilder.CreateCall(fprintFunc, {instructionStrVal});
			}
			std::string separator = "**************** End Of Failing Block *****************\n\n";
			Value *separatorStrVal = elseBuilder.CreateGlobalStringPtr(separator.c_str());
			elseBuilder.CreateCall(fprintFunc, {separatorStrVal});
			

			elseBuilder.CreateBr(thenBB);
		}

		blockCounter++;
	}
	return true;
}

	static void countBasicBlocks(Module *M) {
		for (Function &F : *M) {
			if (!F.isDeclaration()) {
				totalBasicBlocks += std::distance(F.begin(), F.end());
			}
		}
		errs() << "Total basic blocks in module: " << totalBasicBlocks << "\n";
	}
  };
}

unsigned ArithMemDivPass::blockCounter = 1;
unsigned ArithMemDivPass::totalBasicBlocks = 0;
bool ArithMemDivPass::countedBlocks = false;

char ArithMemDivPass::ID = 0;


static RegisterPass<ArithMemDivPass> X("arithmemdivpass", "Insert arithmetic and memory-with-diversity instructions with check", false, false);

static void registerArithMemDivPass(const PassManagerBuilder & Builder, legacy::PassManagerBase &PM) {
	PM.add(new ArithMemDivPass());
}

static RegisterStandardPasses RegisterArithMemDivPass(PassManagerBuilder::EP_OptimizerLast, registerArithMemDivPass);
