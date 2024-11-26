#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Support/ErrorHandling.h"
#include <iterator> 
#include <vector>
#include <map>

using namespace llvm;
static std::map<unsigned, Function*> NoOpFunctionRegistry;

namespace {
	struct ArithmeticPass : public FunctionPass {
		static char ID;
		ArithmeticPass() : FunctionPass(ID) {}


		static unsigned blockCounter; // Basic block ID of the function
		static unsigned totalBasicBlocks; //Total number of basic blocks across functions
		static bool countedBlocks; // Ensure basic blocks are counted only once    
		static unsigned totalFunctions;

		std::string instructionToString(Instruction *I) {
			std::string str;
			llvm::raw_string_ostream(str) << *I;
			return str;
		}

		bool isExcludedInstruction(Instruction *inst) {	
			if (isa<LoadInst>(inst) || isa<StoreInst>(inst) ||
					isa<AtomicCmpXchgInst>(inst) || isa<AtomicRMWInst>(inst) || (isa<LandingPadInst>(inst)) || 
					isa<InsertElementInst>(inst) || isa<AllocaInst>(inst) ||
					isa<InsertValueInst>(inst)|| isa<FenceInst>(inst) || isa<PHINode>(inst)) {
				return true;
			}

			if (isa<LoadInst>(inst)) {
				// Don't duplicate atomic loads
				if (dyn_cast<LoadInst>(inst)->isAtomic()) {
					return true;
				}
				if (dyn_cast<LoadInst>(inst)->isVolatile()) {
					return true;
				}
			}

			if (auto *callInst = dyn_cast<CallInst>(inst)) {
				// Convert tail calls to non-tail calls. It is not safe to insert instructions after tail calls. 
				if (callInst->isTailCall()) {
					callInst->setTailCall(false);
				}

				// Don't duplicate void calls (they do not return a value to compare)
				if (callInst->getType()->isVoidTy()) {
					return true;
				}

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
				return true;
			}
			// Duplicate everything else
			return false;
		}

		bool containsResumeOrCleanupInstruction(BasicBlock &BB) {
			for (Instruction &I : BB) {
				if ((isa<ResumeInst>(&I))||(isa<LandingPadInst>(&I))) {
					return true;
				}
			}
			return false;
		}

		//Exclude Then/Else blocks from getting duplicated. These are blocks added by the instrumentation.
		bool isThenElseBlock(BasicBlock &BB) {
			StringRef name = BB.getName();
			return name.startswith("then") || name.startswith("else");
		}


		// Function to handle operands with the volatile load/store trick
		Value* handleOperand(Value *operand, Function &func, IRBuilder<> &builder, IRBuilder<> &allocaBuilder) {
			if (isa<Constant>(operand)) {
				// If operand is a constant, return it directly without volatile handling
				return operand;
			}
			if (isa<GetElementPtrInst>(operand)) {
				return operand;
			}

			// By putting all the allocas at the beginning of the first basic block of the function (=static allocas), 
			//they get run in the prolog/epilog of the function and therefore they are basically free. 
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
			// These need to be set from the command line. Alternatively, give them a value here.
		  	int blockSize = BLOCKSIZE;
			int interleaving = INTERLEAVING;
			const char* libraryName = LIBRARYNAME;
			
			totalFunctions ++;

			if (isExcludedFunction(&F)) {
				errs() << "Skipping function: " << F.getName() << "\n";
				return true;
			}

			LLVMContext &Ctx = F.getContext();
			errs() << "Running on function: " << F.getName() <<  "  with ID: " <<  totalFunctions << "\n";

			// Use fprintf to print in the stderr (unbuffered)
			FunctionCallee fprintFunc = F.getParent()->getOrInsertFunction(
					"fprintFunc", FunctionType::get(IntegerType::getInt32Ty(Ctx),
						PointerType::get(Type::getInt8Ty(Ctx), 0)));

			FunctionCallee printCPUFunc = F.getParent()->getOrInsertFunction("print_cpu_id",
					FunctionType::get(Type::getVoidTy(Ctx), false));

			FunctionCallee printDateFunc = F.getParent()->getOrInsertFunction("print_date",
					llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), llvm::Type::getInt8PtrTy(Ctx), false));

			if (!countedBlocks) {
				// Count basic blocks on the first invocation
				countBasicBlocks(F.getParent());
				countedBlocks = true;
			}

			// Keep the original basic blocks in a separate structure to keep them unchanged. This is needed because we are adding new basic blocks on the go.
			std::vector<BasicBlock*> bbs;
			for (Function::iterator BI = F.begin(), BE = F.end(); BI != BE; ++BI) {
				BasicBlock *BB = &*BI;
				bbs.push_back(BB);
			}
		
			for (auto BI : bbs) {
				BasicBlock *BB = &*BI;
				if (isThenElseBlock(*BB)) {
					// There shouldn't be any then/else blocks here but double checking.
					continue;
				}

				if (containsResumeOrCleanupInstruction(*BB)) {
					continue;
				}

				std::vector<Instruction*> originalInstructions;

				// The dependency graph is needed for BLOCKSIZE=0 (d), which inserts the check at the end of the instruction dependency chain
				std::map<Instruction*, std::vector<Instruction*>> dependencyGraph;
				for (Instruction &I : *BB) {
					if (&I != BB->getTerminator() && !isExcludedInstruction(&I)) {
						originalInstructions.push_back(&I);
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

				std::map<Instruction*, Instruction*> cloneMap;
				std::vector<std::pair<Value*, Instruction*>> icmpResults;  // Pair of cmp result and instruction string

				Instruction *lastInst = nullptr;  // Declare lastInst outside the loop
				Instruction *clonedLastInst = nullptr;  // Declare clonedLastInst outside the loop

				// Create an IRBuilder for allocas at the beginning of the basic block.
				// This is passed as argument to the handleOperands function
				IRBuilder<> allocaBuilder(BB);
				allocaBuilder.SetInsertPoint(BB->getFirstNonPHI());
				
				unsigned instCounter = 0;
				Instruction *lastOriginalInst = BB->getTerminator(); 
				std::vector<Instruction*> chunkedClonedInsts;	
				IRBuilder <> volbuilderInt0(lastOriginalInst);	
				Instruction *lastOrigInst = nullptr; 
				
				// Loop through each instruction of the basic block
				for (Instruction *Inst : originalInstructions) {
					instCounter++;
					std::vector<Value*> clonedOperands;
					std::vector<Value*> dependencyOperands;

					Instruction *clonedInst = Inst->clone();
					// Make sure the alignment is correct for Loads. Probably not needed
					if (isa<LoadInst>(Inst)) {
						LoadInst *loadInst = dyn_cast<LoadInst>(Inst);
						LoadInst *clonedLoadInst = dyn_cast<LoadInst>(clonedInst);
						clonedLoadInst->setAlignment(loadInst->getAlign());
						clonedInst = clonedLoadInst;
					} 

					for (unsigned i = 0; i < Inst->getNumOperands(); ++i) {
						Value *operand = Inst->getOperand(i);
						if (cloneMap.find(dyn_cast<Instruction>(operand)) != cloneMap.end()) {
							// If there's a duplicate instruction for the operand, use that. This ensures the
							//dependencies are preserved for the duplicate instructions as well.
							dependencyOperands.push_back(cloneMap[dyn_cast<Instruction>(operand)]);
						} else {
							dependencyOperands.push_back(operand);
						}
					}
					for (size_t j = 0; j < dependencyOperands.size(); ++j) {
							clonedInst->setOperand(j, dependencyOperands[j]);
					}
					
					lastOrigInst = Inst;

					// Handle the different interleavings. Add the cloned instructions to their respective chunks
					chunkedClonedInsts.push_back(clonedInst);	
					if (interleaving == 0) {
						//Volatile trick for int0
						bool atleastonehandled = false;
						for (unsigned i = 0; i < clonedInst->getNumOperands(); ++i) {
							Value *operand = clonedInst->getOperand(i);
							if (isa<Constant>(operand)) {
								// If operand is a constant, don't do volatile handling
								clonedOperands.push_back(operand);
							} else {
								atleastonehandled = true;
								Value *volatileOperand;
								volatileOperand = handleOperand(operand, F, volbuilderInt0, allocaBuilder);
								clonedOperands.push_back(volatileOperand); 
							}
						}
						if (atleastonehandled == false) {
							if (isa<LoadInst>(Inst)) {
								if (LoadInst *clonedLoad = dyn_cast<LoadInst>(clonedInst)) {
									clonedLoad->setVolatile(true);
								} else {
									errs() << "Suspicious, I shouldn't be here." << *Inst << "\n";
								}
							} else {
									errs() << "Corner case for volatile trick: " << *Inst << " with argument: " << *(Inst->getOperand(0))  << "\n";
							}
						}	
						// Replace operands in the cloned instruction with their volatile versions or existing clones
						for (size_t j = 0; j < clonedOperands.size(); ++j) {
							clonedInst->setOperand(j, clonedOperands[j]);
						}
						clonedOperands.clear();
						clonedInst->insertBefore(BB->getTerminator());

					} else if (chunkedClonedInsts.size() == interleaving || (instCounter == originalInstructions.size())) {
						// Insert all clones after the current original instruction (Inst)
						for (Instruction *ci : chunkedClonedInsts) {
							ci->insertAfter(lastOrigInst);  
							IRBuilder <> volbuilderIntX(ci);	
							
							//Volatile trick
							bool atleastonehandled = false;
							for (unsigned i = 0; i < ci->getNumOperands(); ++i) {
								Value *operand = ci->getOperand(i);
								if (isa<Constant>(operand)) {
									// If operand is a constant, don't do volatile handling
									clonedOperands.push_back(operand);
								} else {
									atleastonehandled = true;
									Value *volatileOperand;
									volatileOperand = handleOperand(operand, F, volbuilderIntX, allocaBuilder);
									clonedOperands.push_back(volatileOperand); 
								}
							}
							if (atleastonehandled == false) {
								if (isa<LoadInst>(Inst)) {
									if (LoadInst *clonedLoad = dyn_cast<LoadInst>(ci)) {
										clonedLoad->setVolatile(true);
									} else {
										errs() << "Suspicious, I shouldn't be here. " << *Inst << "\n";
									}
								} else {
										errs() << "Corner case for volatile trick: " << *Inst << " with argument: " << *(Inst->getOperand(0))  << "\n";
								}
							}
							// Replace operands in the cloned instruction with their volatile versions or existing clones
							for (size_t j = 0; j < clonedOperands.size(); ++j) {
								ci->setOperand(j, clonedOperands[j]);
							}
							clonedOperands.clear();

							lastOrigInst = ci;  // Update Inst to the cloned instruction, so the next clone is inserted after it
						}
						// Clear the cloned instructions vector
						chunkedClonedInsts.clear();
					}
					
					cloneMap[Inst] = clonedInst;
				
					if (!Inst->getType()->isVoidTy()) {
						lastInst = Inst;
						clonedLastInst = clonedInst;
					} else if (isa<CallInst>(Inst) && Inst->getType()->isVoidTy()) {
						continue;
					} else {
						errs() << "ERROR: My instruction is nullptr." << "\n";
					}

					Instruction *lastInst = originalInstructions[instCounter - 1];
					//Insert the comparisons based on type.
					if ((blockSize == 0 && (std::find(independentClusters.begin(), independentClusters.end(), lastInst) != independentClusters.end()))
					|| (blockSize !=0 && (instCounter % blockSize == 0 || instCounter == originalInstructions.size()))) {
						Instruction *clonedLastInst = cloneMap[lastInst];

						IRBuilder<> builder(BB->getTerminator());
						Value *cmp = nullptr;

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
									auto *intType = builder.getIntPtrTy(lastInst->getModule()->getDataLayout());
									Value *intVal1 = builder.CreatePtrToInt(elem1, intType, "ptr_to_int1");
									Value *intVal2 = builder.CreatePtrToInt(elem2, intType, "ptr_to_int2");
									elemCmp = builder.CreateICmpEQ(intVal1, intVal2, "ptr_cmp_result");
								} else {
									errs() << "Unsupported vector element type for comparison for: " << *lastInst<< " with type: ";
									lastInst->getType()->print(errs());
									errs() << "\n";
									vectorCmp = nullptr;
									break;
								}
								vectorCmp = builder.CreateAnd(vectorCmp, elemCmp, "vec_cmp_agg");
							}
							cmp = vectorCmp;
							if (cmp == nullptr) {
								errs() << "Vector comparison failed!" << *(Inst) << "\n";
							}
						} else if (lastInst->getType()->isPointerTy() || clonedLastInst->getType()->isPointerTy()) {
							auto *intType = builder.getIntPtrTy(lastInst->getModule()->getDataLayout());
							Value *intVal1 = builder.CreatePtrToInt(lastInst, intType, "ptr_to_int1");
							Value *intVal2 = builder.CreatePtrToInt(clonedLastInst, intType, "ptr_to_int2");
							cmp = builder.CreateICmpEQ(intVal1, intVal2, "ptr_cmp_result");
						} else if (isa<StructType>(lastInst->getType())) {
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
											auto *intType = builder.getIntPtrTy(lastInst->getModule()->getDataLayout());
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
										errs() << "Struct comparison failed!" << *(Inst) << "\n";
									}
								}
							}
						}  else {
							errs() << "!!!!!! FIX IT: NO_COMPARISON SUPPORTED YET for instruction: " << *Inst << " is of type: ";
							lastInst->getType()->print(errs());
							errs() << "\n";
						}
						if (cmp) {
							icmpResults.push_back(std::make_pair(cmp, lastInst));
						}
					}
				}
				
				// Create the comparison by aggregating the results of all icmp instructions and create the corresponding then/else blocks

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
					llvm::Value* libraryNameArg = elseBuilder.CreateGlobalStringPtr(LIBRARYNAME);
					elseBuilder.CreateCall(printDateFunc, libraryNameArg);

					Value* funcName = elseBuilder.CreateGlobalStringPtr(F.getName());
					Value* blockIdValue = ConstantInt::get(Type::getInt32Ty(Ctx), blockCounter);
					Value * functionStr = elseBuilder.CreateGlobalStringPtr("Error in function: %s , #Basic block: %d \n \0");
					elseBuilder.CreateCall(fprintFunc, {functionStr, funcName, blockIdValue});					

					for (auto &icmpPair : icmpResults) {
						Instruction * origInstr = icmpPair.second;
						std::string origInstrStr = instructionToString(origInstr);
						Value *instName = elseBuilder.CreateGlobalStringPtr(origInstrStr.c_str());
						auto clonedInstrItr = cloneMap.find(origInstr);
						if (clonedInstrItr == cloneMap.end()) {
							errs() << "ERROR: No instruction in cloneMap!" << "\n";
						}

						if (Instruction *originalInst = dyn_cast<Instruction>(icmpPair.first)) {
							Instruction * clonedInstr = cloneMap[origInstr];
							Type * instReturnType1 = origInstr->getType();
							Type * instReturnType2 = clonedInstr->getType();

							Value * formatStr = elseBuilder.CreateGlobalStringPtr("Potential Failing Instruction: %s \n");
							Value * newLine = elseBuilder.CreateGlobalStringPtr("\n");

							//Create the values for the memset call parameters
							Value *Zero = elseBuilder.getInt8(0);

							//Since the allocation of space for the printing is happening at compile time, 
							//it could be the case that this changes at runtime after the optimizations are performed. 
							//For this reason, we allocate a big enough constant amount of space (64 bytes) for all instructions
							//Probably uneccessary and can be removed.
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
							PointerType *origin_ptr = PointerType::getUnqual(origInstr->getType());
							PointerType *cloned_ptr = PointerType::getUnqual(clonedInstr->getType());

							Value *castedPtr1 = elseBuilder.CreateBitCast(allocaInstr1, origin_ptr);
							Value *castedPtr2 = elseBuilder.CreateBitCast(allocaInstr2, cloned_ptr);

							StoreInst* storeInstr1 = elseBuilder.CreateStore(origInstr, castedPtr1, true);
							StoreInst* storeInstr2 = elseBuilder.CreateStore(clonedInstr, castedPtr2, true);

							TypeSize size1 = F.getParent()->getDataLayout().getTypeStoreSize(allocaInstr1->getAllocatedType());
							TypeSize size2 = F.getParent()->getDataLayout().getTypeStoreSize(allocaInstr2->getAllocatedType());

							Value * addr1 = storeInstr1->getOperand(1);
							Value * addr2 = storeInstr2->getOperand(1);

							Value * castedAddr1 = elseBuilder.CreatePointerCast(addr1, Type::getInt8PtrTy(Ctx), "pointerCast");
							Value * castedAddr2 = elseBuilder.CreatePointerCast(addr2, Type::getInt8PtrTy(Ctx), "pointerCast");

							FunctionCallee pp = F.getParent()->getOrInsertFunction("printMemoryAsHex", Type::getInt32PtrTy(Ctx), Type::getInt8PtrTy(Ctx), Type::getInt32Ty(Ctx), Type::getInt8PtrTy(Ctx), Type::getInt32Ty(Ctx));
							
							// Incr_err sets a limit to the amount of errors we want to print. Currently disabled.
							//FunctionCallee incr_err = F.getParent()->getOrInsertFunction("incr_err", Type::getInt32PtrTy(Ctx), Type::getInt32Ty(Ctx), Type::getInt32Ty(Ctx));

							Value * size_bytes1 = ConstantInt::get(Type::getInt32Ty(Ctx), size1, false);
							Value * size_bytes2 = ConstantInt::get(Type::getInt32Ty(Ctx), size2, false);

							Value * bb_index = ConstantInt::get(Type::getInt32Ty(Ctx), blockCounter, false);
							Value * bb_total = ConstantInt::get(Type::getInt32Ty(Ctx), totalBasicBlocks, false);

							elseBuilder.CreateCall(fprintFunc, {formatStr, instName});
							elseBuilder.CreateCall(pp, {castedAddr1, size_bytes1, castedAddr2, size_bytes2});
							elseBuilder.CreateCall(fprintFunc, {newLine});
						}
					}

					// Uncomment for more info printed but slower build process
					/*
					std::string separator1 = "Beginning Of Failing Block:\n";
					Value *separatorStrVal1 = elseBuilder.CreateGlobalStringPtr(separator1.c_str());
					elseBuilder.CreateCall(fprintFunc, {separatorStrVal1});
					for (Instruction &I : *BB) {
						std::string instructionStr = instructionToString(&I) + "\n";
						Value *instructionStrVal = elseBuilder.CreateGlobalStringPtr(instructionStr.c_str());
						elseBuilder.CreateCall(fprintFunc, {instructionStrVal});
					}
					std::string separator = "End Of Failing Block:\n\n";
					Value *separatorStrVal = elseBuilder.CreateGlobalStringPtr(separator.c_str());
					elseBuilder.CreateCall(fprintFunc, {separatorStrVal});
					*/

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
			// errs() << "Total basic blocks in module: " << totalBasicBlocks << "\n";
		}
	};
}

unsigned ArithmeticPass::blockCounter = 1;
unsigned ArithmeticPass::totalBasicBlocks = 0;
bool ArithmeticPass::countedBlocks = false;
unsigned ArithmeticPass::totalFunctions = 0;

char ArithmeticPass::ID = 0;


static RegisterPass<ArithmeticPass> X("arithmeticpass", "ITHICA_A: Duplicate arithmetic instructions and compare", false, false);

static void registerArithmeticPass(const PassManagerBuilder & Builder, legacy::PassManagerBase &PM) {
	PM.add(new ArithmeticPass());
}

static RegisterStandardPasses RegisterArithmeticPass(PassManagerBuilder::EP_OptimizerLast, registerArithmeticPass);
