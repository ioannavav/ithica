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
#include "llvm/IR/Operator.h"
#include "llvm/Support/ErrorHandling.h"
#include <iterator> 
#include <vector>
#include <map>
#include <set>

using namespace llvm;
static std::map<unsigned, Function*> NoOpFunctionRegistry;
static const bool UseVolatile = true;  // for redundancy preservation

namespace {
	struct ArithMemPass : public FunctionPass {
		static char ID;
		ArithMemPass() : FunctionPass(ID) {}

		enum class ArithPolicy { Instrument, Exclude, Unknown };

		static unsigned blockCounter; // Basic block ID of the function
		static unsigned totalBasicBlocks; //Total number of basic blocks across functions
		static bool countedBlocks; // Ensure basic blocks are counted only once    
		static unsigned totalFunctions; //Total number of functions processed

		std::string instructionToString(Instruction *I) {
			std::string str;
			llvm::raw_string_ostream(str) << *I;
			return str;
		}

		ArithPolicy classifyCall(CallInst *callInst) {
			if (callInst->getType()->isVoidTy() || callInst->isMustTailCall() ||
					callInst->cannotDuplicate() || callInst->isConvergent()) {
				return ArithPolicy::Exclude;
			}
			if (callInst->mayHaveSideEffects()) {
				return ArithPolicy::Exclude;
			}
			if (callInst->isInlineAsm()) {
				InlineAsm *inlineAsm = dyn_cast<InlineAsm>(callInst->getCalledOperand());
				if (inlineAsm && inlineAsm->getAsmString().find("syscall") != std::string::npos) {
					return ArithPolicy::Exclude;
				}
				return callInst->doesNotAccessMemory() ?
						ArithPolicy::Instrument : ArithPolicy::Exclude;  
			}
			Function *calledFunction = callInst->getCalledFunction();
			if (calledFunction && calledFunction->isIntrinsic() &&
					callInst->doesNotAccessMemory()) {
				return ArithPolicy::Instrument;
			}
			return ArithPolicy::Exclude;
		}

		ArithPolicy classifyInstruction(Instruction *inst) {
			// Calls have separate attribute and inline-assembly checks.
			if (auto *callInst = dyn_cast<CallInst>(inst)) {
				return classifyCall(callInst);
			}

			if (auto *fpOp = dyn_cast<FPMathOperator>(inst)) {
				if (fpOp->getFastMathFlags().any()) {
					return ArithPolicy::Exclude;
				}
			}

			// Explicit exclusions fail side-effect freedom (C1), determinism (C2),
			// or have no independently comparable result.
			if (inst->isTerminator() || isa<LoadInst>(inst) || isa<StoreInst>(inst) ||
					isa<AtomicCmpXchgInst>(inst) || isa<AtomicRMWInst>(inst) ||
					isa<AllocaInst>(inst) || isa<FenceInst>(inst) || isa<PHINode>(inst) ||
					isa<LandingPadInst>(inst) || isa<FuncletPadInst>(inst) ||
					isa<InsertElementInst>(inst) || isa<InsertValueInst>(inst) ||
					isa<FreezeInst>(inst) || isa<VAArgInst>(inst) || isa<CallBase>(inst)) {
				return ArithPolicy::Exclude;
			}

			// Explicit allowlist for supported arithmetic/computational instructions.
			if (isa<BinaryOperator>(inst) || isa<UnaryOperator>(inst) ||
					isa<CastInst>(inst) || isa<CmpInst>(inst) ||
					isa<SelectInst>(inst) || isa<GetElementPtrInst>(inst) ||
					isa<ExtractElementInst>(inst) || isa<ShuffleVectorInst>(inst) ||
					isa<ExtractValueInst>(inst)) {
				return ArithPolicy::Instrument;
			}

			errs() << "ITHICA ArithMemPass: unclassified opcode '"
				   << inst->getOpcodeName()
				   << "' is not instrumented; add it to the Instrument or Exclude "
					  "set in classifyInstruction()\n";
			return ArithPolicy::Unknown;
		}

		void prepareForInstrumentation(Instruction *inst) {
			if (auto *callInst = dyn_cast<CallInst>(inst)) {
				if (callInst->isTailCall() && !callInst->isMustTailCall()) {
					callInst->setTailCall(false);
				}
			}
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
			if (!UseVolatile) {
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

		void remapCloneDependencies(
				Instruction *clonedInst,
				const std::map<Instruction*, Instruction*> &cloneMap) {
			for (unsigned i = 0; i < clonedInst->getNumOperands(); ++i) {
				auto *operandInst = dyn_cast<Instruction>(clonedInst->getOperand(i));
				auto clonedOperand = cloneMap.find(operandInst);
				if (clonedOperand != cloneMap.end()) {
					clonedInst->setOperand(i, clonedOperand->second);
				}
			}
		}

		bool isClonedValue(Value *V,
				const std::map<Instruction*, Instruction*> &cloneMap) {
			auto *inst = dyn_cast<Instruction>(V);
			if (!inst) {
				return false;
			}
			// cloneMap holds original -> clone. A value is a "clone result" iff it
			// is the mapped-to instruction of some entry. 
			for (const auto &entry : cloneMap) {
				if (entry.second == inst) {
					return true;
				}
			}
			return false;
		}

		void prepareCloneOperands(
				Instruction *originalInst, Instruction *clonedInst,
				Function &F, IRBuilder<> &builder, IRBuilder<> &allocaBuilder,
				const std::map<Instruction*, Instruction*> &cloneMap) {
			std::vector<Value*> clonedOperands;
			bool anyBarriered = false;      // did a real barrier get inserted
			bool anySkippedByDesign = false; // constant / already-a-clone

			for (Use &U : clonedInst->operands()) {
				Value *operand = U.get();
				if (isa<Constant>(operand)) {
					anySkippedByDesign = true;
					clonedOperands.push_back(operand);
				} else if (isClonedValue(operand, cloneMap)) {
					// Leaf-only (default). For full redundancy, replace the two lines below
					// with the two commented lines (barriers intermediate clone results too,
					// so the optimizer can't collapse invertible chains).
					anySkippedByDesign = true;
					clonedOperands.push_back(operand);
					// anyBarriered = true;
					// clonedOperands.push_back(handleOperand(operand, F, builder, allocaBuilder));
				} else {
					anyBarriered = true;
					clonedOperands.push_back(
							handleOperand(operand, F, builder, allocaBuilder));
				}
			}

			if (!anyBarriered && !anySkippedByDesign) {
				if (isa<LoadInst>(originalInst)) {
					if (auto *clonedLoad = dyn_cast<LoadInst>(clonedInst)) {
						clonedLoad->setVolatile(true);
					} else {
						errs() << "Suspicious: expected a load clone but found none: "
							   << *originalInst << "\n";
					}
				} else {
					errs() << "Warning: no barrier inserted where one was expected: "
						   << *originalInst << "\n";
				}
			}

			for (size_t i = 0; i < clonedOperands.size(); ++i) {
				clonedInst->setOperand(i, clonedOperands[i]);
			}
		}

		// Non-volatile, non-atomic loads/stores are instrumented via the memory path.
		bool isMemoryInstrumentable(Instruction *inst) {
			if (auto *li = dyn_cast<LoadInst>(inst)) {
				return !li->isAtomic() && !li->isVolatile();
			}
			if (auto *si = dyn_cast<StoreInst>(inst)) {
				return !si->isAtomic() && !si->isVolatile();
			}
			return false;
		}
		
		bool isExcludedFunction(Function *F) {
			static const std::set<std::string> ExcludedFunctions = {
				"Function_name_to_exclude_"
			};
			for (const auto &excludedName : ExcludedFunctions) {
				if (F->getName().str().find(excludedName) != std::string::npos) {
					return true;
				}
			}
			return false;
		}


		// i1 iff a==b; FP bitwise; aggregates element-wise. nullptr = unsupported.
		Value *emitEqualityCheck(IRBuilder<> &B, Value *a, Value *b, const DataLayout &DL) {
			Type *T = a->getType();
			LLVMContext &C = B.getContext();

			if (T->isIntegerTy()) {
				return B.CreateICmpEQ(a, b, "cmp_result" + std::to_string(blockCounter));
			}
			if (T->isFloatingPointTy()) {
				// Compare the raw bits so that bit-identical NaNs count as equal.
				unsigned bits = T->getScalarSizeInBits();
				Type *intTy = IntegerType::get(C, bits);
				Value *ia = B.CreateBitCast(a, intTy, "fp_bits1");
				Value *ib = B.CreateBitCast(b, intTy, "fp_bits2");
				return B.CreateICmpEQ(ia, ib, "cmp_result" + std::to_string(blockCounter));
			}
			if (T->isPointerTy()) {
				Type *intTy = B.getIntPtrTy(DL);
				Value *ia = B.CreatePtrToInt(a, intTy, "ptr_to_int1");
				Value *ib = B.CreatePtrToInt(b, intTy, "ptr_to_int2");
				return B.CreateICmpEQ(ia, ib, "ptr_cmp_result");
			}
			if (auto *vecTy = dyn_cast<VectorType>(T)) {
				unsigned numElements = vecTy->getElementCount().getKnownMinValue();
				Value *agg = ConstantInt::getTrue(C);
				for (unsigned i = 0; i < numElements; ++i) {
					Value *idx = ConstantInt::get(Type::getInt32Ty(C), i);
					Value *e1 = B.CreateExtractElement(a, idx, "vec_elem1");
					Value *e2 = B.CreateExtractElement(b, idx, "vec_elem2");
					Value *ec = emitEqualityCheck(B, e1, e2, DL);
					if (!ec) return nullptr;
					agg = B.CreateAnd(agg, ec, "vec_cmp_agg");
				}
				return agg;
			}
			if (auto *structTy = dyn_cast<StructType>(T)) {
				unsigned numElements = structTy->getNumElements();
				Value *agg = ConstantInt::getTrue(C);
				for (unsigned i = 0; i < numElements; ++i) {
					Value *e1 = B.CreateExtractValue(a, i, "struct_elem1");
					Value *e2 = B.CreateExtractValue(b, i, "struct_elem2");
					Value *ec = emitEqualityCheck(B, e1, e2, DL);
					if (!ec) return nullptr;
					agg = B.CreateAnd(agg, ec, "struct_cmp_agg");
				}
				return agg;
			}
			if (auto *arrTy = dyn_cast<ArrayType>(T)) {
				unsigned numElements = (unsigned)arrTy->getNumElements();
				Value *agg = ConstantInt::getTrue(C);
				for (unsigned i = 0; i < numElements; ++i) {
					Value *e1 = B.CreateExtractValue(a, i, "arr_elem1");
					Value *e2 = B.CreateExtractValue(b, i, "arr_elem2");
					Value *ec = emitEqualityCheck(B, e1, e2, DL);
					if (!ec) return nullptr;
					agg = B.CreateAnd(agg, ec, "arr_cmp_agg");
				}
				return agg;
			}
			return nullptr;
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
			
			totalFunctions ++;

			if (isExcludedFunction(&F)) {
				errs() << "Skipping function: " << F.getName() << "\n";
				return false;
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
				std::vector<Value*> originalValues; // for stores

				// The dependency graph is needed for BLOCKSIZE=0 (d), which inserts the check at the end of the instruction dependency chain
				std::map<Instruction*, std::vector<Instruction*>> dependencyGraph;
				for (Instruction &I : *BB) {
					ArithPolicy policy = classifyInstruction(&I);
					bool mem = isMemoryInstrumentable(&I);
					if (policy == ArithPolicy::Instrument || mem) {
						if (policy == ArithPolicy::Instrument) {
							prepareForInstrumentation(&I);
						}
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
				std::map<Instruction*, Value*> InstToValueMap; // for stores
				std::vector<std::pair<Value*, Instruction*>> icmpResults;  // Pair of cmp result and instruction string

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
					
					Instruction *clonedInst = nullptr;
					
					if (isa<StoreInst>(Inst)) {
						// Memory: duplicate the store with an adjacent volatile reload.
						IRBuilder<> storeBuilder(BB);
						storeBuilder.SetInsertPoint(Inst->getNextNode());
						Value *storedValue = Inst->getOperand(0);
						Value *storeAddress = Inst->getOperand(1);
						if (!storeAddress->getType()->isPointerTy()) {
							errs() << "Store address is not a pointer type: " << *storeAddress << "\n";
							continue;
						}
						if (isa<ConstantPointerNull>(storeAddress)) {
							errs() << "Store address is a constant null pointer: " << *storeAddress << "\n";
							continue;
						}
						LoadInst *reloadedValue = storeBuilder.CreateLoad(storedValue->getType(), storeAddress, true);
						reloadedValue->setAlignment(dyn_cast<StoreInst>(Inst)->getAlign());
						reloadedValue->setVolatile(true);
						clonedInst = reloadedValue;
						originalValues[instCounter - 1] = storedValue;
						InstToValueMap[Inst] = storedValue;
						cloneMap[Inst] = clonedInst;
					} else if (isa<LoadInst>(Inst)) {
						// Memory: duplicate the load with an adjacent volatile load.
						clonedInst = Inst->clone();
						LoadInst *loadInst = dyn_cast<LoadInst>(Inst);
						LoadInst *clonedLoadInst = dyn_cast<LoadInst>(clonedInst);
						clonedLoadInst->setAlignment(loadInst->getAlign());
						clonedLoadInst->setVolatile(true);
						clonedInst = clonedLoadInst;
						remapCloneDependencies(clonedInst, cloneMap);
						clonedInst->insertAfter(Inst);
						cloneMap[Inst] = clonedInst;
					} else {
						// Arithmetic: duplicate with operand barriers and chunked interleaving.
						clonedInst = Inst->clone();
						remapCloneDependencies(clonedInst, cloneMap);
						lastOrigInst = Inst;
						chunkedClonedInsts.push_back(clonedInst);
						if (interleaving == 0) {
							prepareCloneOperands(Inst, clonedInst, F, volbuilderInt0, allocaBuilder, cloneMap);
							clonedInst->insertBefore(BB->getTerminator());
						} else if (chunkedClonedInsts.size() == interleaving || (instCounter == originalInstructions.size())) {
							for (Instruction *ci : chunkedClonedInsts) {
								ci->insertAfter(lastOrigInst);
								IRBuilder<> volbuilderIntX(ci);
								prepareCloneOperands(Inst, ci, F, volbuilderIntX, allocaBuilder, cloneMap);
								lastOrigInst = ci;
							}
							chunkedClonedInsts.clear();
						}
						cloneMap[Inst] = clonedInst;
					}
					
					// Void arith calls have no comparable result; stores compare via the stored value.
					if (Inst->getType()->isVoidTy() && !isa<StoreInst>(Inst)) {
						if (isa<CallInst>(Inst)) {
							continue;
						}
						errs() << "Error: Instruction is nullptr." << "\n";
					}
					
					Value *lastValue = nullptr;
					Instruction *lastInst = originalInstructions[instCounter - 1];
					if (isa<StoreInst>(Inst)) {
						lastValue = originalValues[instCounter - 1];
					}
					// Insert the comparisons based on type.
					if ((blockSize == 0 && (std::find(independentClusters.begin(), independentClusters.end(), lastInst) != independentClusters.end()))
					|| (blockSize !=0 && (instCounter % blockSize == 0 || instCounter == originalInstructions.size()))) {
						Instruction *clonedLastInst = cloneMap[lastInst];
						IRBuilder<> builder(BB->getTerminator());
						Value *origForCmp = lastValue ? lastValue : lastInst;
						Value *cmp = emitEqualityCheck(builder, origForCmp, clonedLastInst,
							F.getParent()->getDataLayout());
						if (!cmp) {
							errs() << "No comparison supported for instruction: " << *Inst << " is of type: ";
							origForCmp->getType()->print(errs());
							errs() << "\n";
						}
						if (cmp) {
							icmpResults.push_back(std::make_pair(cmp, lastInst));
						}
					}
				}
				
				// Flush arithmetic clones still pending (e.g. when the last instrumented
				// instruction was a load/store, which does not trigger the in-loop flush).
				if (!chunkedClonedInsts.empty()) {
					for (Instruction *ci : chunkedClonedInsts) {
						ci->insertAfter(lastOrigInst);
						IRBuilder<> volbuilderIntX(ci);
						prepareCloneOperands(ci, ci, F, volbuilderIntX, allocaBuilder, cloneMap);
						lastOrigInst = ci;
					}
					chunkedClonedInsts.clear();
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
					llvm::Value* libraryNameArg = elseBuilder.CreateGlobalStringPtr(libraryName);
					elseBuilder.CreateCall(printDateFunc, libraryNameArg);

					Value* funcName = elseBuilder.CreateGlobalStringPtr(F.getName());
					Value* blockIdValue = ConstantInt::get(Type::getInt32Ty(Ctx), blockCounter);
					Value * functionStr = elseBuilder.CreateGlobalStringPtr("Error in function: %s , #Basic block: %d \n \0");
					elseBuilder.CreateCall(fprintFunc, {functionStr, funcName, blockIdValue});					

					for (auto &icmpPair : icmpResults) {
						Instruction * origInstr = icmpPair.second;
						Value *origForDump = isa<StoreInst>(origInstr) ? InstToValueMap[origInstr] : (Value*)origInstr;
						std::string origInstrStr = instructionToString(origInstr);
						Value *instName = elseBuilder.CreateGlobalStringPtr(origInstrStr.c_str());
						auto clonedInstrItr = cloneMap.find(origInstr);
						if (clonedInstrItr == cloneMap.end()) {
							errs() << "Error: No instruction in cloneMap!" << "\n";
						}

						if (isa<Instruction>(icmpPair.first)) {
							Instruction * clonedInstr = cloneMap[origInstr];

							Value * formatStr = elseBuilder.CreateGlobalStringPtr("Potential Failing Instruction: %s \n");
							Value * newLine = elseBuilder.CreateGlobalStringPtr("\n");

							//Create the values for the memset call parameters
							Value *Zero = elseBuilder.getInt8(0);

							//Since the allocation of space for the printing is happening at compile time, 
							//it could be the case that this changes at runtime after the optimizations are performed. 
							//For this reason, we allocate a big enough constant amount of space (64 bytes) for all instructions
							//Probably uneccessary and can be removed.
							// Scratch buffers for the hex dump, sized to hold each value (min 64 bytes)
							const DataLayout &DL = F.getParent()->getDataLayout();
							uint64_t bufBytes1 = DL.getTypeStoreSize(origForDump->getType());
							uint64_t bufBytes2 = DL.getTypeStoreSize(clonedInstr->getType());
							if (bufBytes1 < 64) bufBytes1 = 64;
							if (bufBytes2 < 64) bufBytes2 = 64;
							Align bufAlign1 = DL.getABITypeAlign(origForDump->getType());
							Align bufAlign2 = DL.getABITypeAlign(clonedInstr->getType());
							if (bufAlign1 < Align(8)) bufAlign1 = Align(8);
							if (bufAlign2 < Align(8)) bufAlign2 = Align(8);

							// Create byte arrays sized to hold each value (min 64 bytes)
							ArrayType* Int64ArrayType1 = ArrayType::get(Zero->getType(), bufBytes1);
							ArrayType* Int64ArrayType2 = ArrayType::get(Zero->getType(), bufBytes2);

							AllocaInst* allocaInstr1 = elseBuilder.CreateAlloca(Int64ArrayType1, nullptr, "alloca1");
							AllocaInst* allocaInstr2 = elseBuilder.CreateAlloca(Int64ArrayType2, nullptr, "alloca2");
							allocaInstr1->setAlignment(bufAlign1);
							allocaInstr2->setAlignment(bufAlign2);

							elseBuilder.CreateMemSet(allocaInstr1, Zero, elseBuilder.getInt32(bufBytes1), bufAlign1, true);
							elseBuilder.CreateMemSet(allocaInstr2, Zero, elseBuilder.getInt32(bufBytes2), bufAlign2, true);

							// Create store instructions in the else block
							PointerType *origin_ptr = PointerType::getUnqual(origForDump->getType());
							PointerType *cloned_ptr = PointerType::getUnqual(clonedInstr->getType());

							Value *castedPtr1 = elseBuilder.CreateBitCast(allocaInstr1, origin_ptr);
							Value *castedPtr2 = elseBuilder.CreateBitCast(allocaInstr2, cloned_ptr);

							StoreInst* storeInstr1 = elseBuilder.CreateStore(origForDump, castedPtr1, true);
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

							elseBuilder.CreateCall(fprintFunc, {formatStr, instName});
							elseBuilder.CreateCall(pp, {castedAddr1, size_bytes1, castedAddr2, size_bytes2});
							elseBuilder.CreateCall(fprintFunc, {newLine});
						}
					}

					// Uncomment the following code for more info printed upon error detectionbut slower build process
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

unsigned ArithMemPass::blockCounter = 1;
unsigned ArithMemPass::totalBasicBlocks = 0;
bool ArithMemPass::countedBlocks = false;
unsigned ArithMemPass::totalFunctions = 0;

char ArithMemPass::ID = 0;

static RegisterPass<ArithMemPass> X("arithmempass", "ITHICA_AM: Duplicate arithmetic + memory instructions and compare", false, false);

static void registerArithMemPass(const PassManagerBuilder & Builder, legacy::PassManagerBase &PM) {
	PM.add(new ArithMemPass());
}
static RegisterStandardPasses RegisterArithMemPass(PassManagerBuilder::EP_OptimizerLast, registerArithMemPass);
