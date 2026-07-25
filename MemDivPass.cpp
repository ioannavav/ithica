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
#include <set>

using namespace llvm;
static std::map<unsigned, Function*> NoOpFunctionRegistry;

namespace {
    struct MemDivPass : public FunctionPass {
        static char ID;
        MemDivPass() : FunctionPass(ID) {}

        static unsigned blockCounter; // Basic block ID of the function
        static unsigned totalBasicBlocks; // Total number of basic blocks across functions
        static bool countedBlocks; // Ensure basic blocks are counted only once
        static unsigned totalFunctions; // Total number of functions processed

        std::string instructionToString(Instruction *I) {
            std::string str;
            llvm::raw_string_ostream rso(str);
            I->print(rso);
            rso.flush();
            return str;
        }

        bool isExcludedInstruction(Instruction *inst) {

            if (!isa<StoreInst>(inst) && !isa<LoadInst>(inst)) {
                return true;
            }

            if (isa<LoadInst>(inst)) {
                // Don't duplicate atomic loads
                if (dyn_cast<LoadInst>(inst)->isAtomic()) {
                    errs() << "Skipping atomic load instruction: " << *inst << "\n";
                    return true;
                }
                // Don't duplicate volatile loads
                if (dyn_cast<LoadInst>(inst)->isVolatile()) {
                    errs() << "Skipping volatile load instruction: " << *inst << "\n";
                    return true;
                }
            }

            if (isa<StoreInst>(inst)) {
                // Don't duplicate atomic stores
                if (dyn_cast<StoreInst>(inst)->isAtomic()) {
                    errs() << "Skipping atomic store instruction: " << *inst << "\n";
                    return true;
                }
                // Don't duplicate volatile stores
                if (dyn_cast<StoreInst>(inst)->isVolatile()) {
                    errs() << "Skipping volatile store instruction: " << *inst << "\n";
                    return true;
                }
            }
            // Include all other loads/stores
            return false;
        }

        bool containsResumeOrCleanupInstruction(BasicBlock &BB) {
            for (Instruction &I : BB) {
                if ((isa<ResumeInst>(&I)) || (isa<LandingPadInst>(&I))) {
                    return true;
                }
            }
            return false;
        }

        // Exclude Then/Else blocks from getting duplicated. These are blocks added by the instrumentation.
        bool isThenElseBlock(BasicBlock &BB) {
            StringRef name = BB.getName();
            return name.startswith("then") || name.startswith("else");
        }

        bool isExcludedFunction(Function *F) {
            static const std::set<std::string> ExcludedFunctions = {
                // "Add function to exclude"
                "ossl_lh_strcasehash", "OPENSSL_LH_insert", "CRYPTO_set_ex_data", "ossl_sa_set",
                "CRYPTO_zalloc", "OPENSSL_LH_doall_arg", "obj_name_cmp", "_ZN8tcmalloc17tcmalloc_internal", "SymbolizeEPK"
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

            totalFunctions++;

            if (isExcludedFunction(&F)) {
                errs() << "Skipping function: " << F.getName() << "\n";
                return false;
            }

            LLVMContext &Ctx = F.getContext();
            errs() << "Running on function: " << F.getName() <<  "  with ID: " <<  totalFunctions << "\n";

            // Use fprintf to print in the stderr (unbuffered)
            FunctionCallee fprintFunc = F.getParent()->getOrInsertFunction(
                    "fprintFunc", FunctionType::get(Type::getVoidTy(Ctx),
                        Type::getInt8PtrTy(Ctx), true));

            FunctionCallee printCPUFunc = F.getParent()->getOrInsertFunction("print_cpu_id",
                    FunctionType::get(Type::getVoidTy(Ctx), false));

            FunctionCallee printDateFunc = F.getParent()->getOrInsertFunction("print_date",
                    llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), llvm::Type::getInt8PtrTy(Ctx), false));

            if (!countedBlocks) {
                // Count basic blocks on the first invocation
                countBasicBlocks(F.getParent());
                countedBlocks = true;
            }

            // Keep the original basic blocks in a separate structure to keep them unchanged. This is needed because we are adding new basic blocks on the go
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
                std::vector<Value*> originalValues; // For Stores

                // The dependency graph is needed for BLOCKSIZE=0 (d), which inserts the check at the end of the instruction dependency chain
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
                std::map<Instruction*, Value*> InstToValueMap; // For Stores
                std::vector<std::tuple<Value*, Instruction*, Instruction*>> icmpResults;

                Instruction *lastInst = nullptr;  // Declare lastInst outside the loop
                Instruction *clonedLastInst = nullptr;  // Declare clonedLastInst outside the loop

                // Create an IRBuilder for allocas at the beginning of the basic block.
                IRBuilder<> allocaBuilder(BB);
                allocaBuilder.SetInsertPoint(BB->getFirstNonPHI());

                unsigned instCounter = 0;

                // Aliasing protection
                std::vector<std::pair<Instruction*, Value*>> pendingLoadClones;
                Instruction *lastLoadInst = nullptr; // anchor: insert the batch after this load
                Instruction *prevInst = nullptr;     // previous instrumented op, for gap scanning
                int maxLoadBatch = (interleaving <= 0)
                        ? (int)originalInstructions.size() + 1 : interleaving;
                auto flushLoadClones = [&](Instruction *anchor) {
                    Instruction *at = anchor;
                    for (auto &pr : pendingLoadClones) {
                        Instruction *clone = pr.first;
                        Value *loadPtr = pr.second;
                        // Memory diversity
                        // IRBuilder<> mfenceBuilder(BB);
                        // mfenceBuilder.SetInsertPoint(at->getNextNode());
                        // InlineAsm *mfenceAsm = InlineAsm::get(FunctionType::get(Type::getVoidTy(F.getContext()), false), "mfence", "", true);
                        // CallInst *mfenceCall = mfenceBuilder.CreateCall(mfenceAsm);
                        // at = mfenceCall;
                        IRBuilder<> clflushBuilder(BB);
                        clflushBuilder.SetInsertPoint(at->getNextNode());
                        InlineAsm *clflushAsm = InlineAsm::get(
                                FunctionType::get(Type::getVoidTy(F.getContext()), loadPtr->getType(), false),
                                "clflush $0", "m", true);
                        CallInst *clflushCall = clflushBuilder.CreateCall(clflushAsm, loadPtr);
                        at = clflushCall;
                        clone->insertAfter(at);
                        at = clone;
                    }
                    pendingLoadClones.clear();
                };
                auto writeBetween = [&](Instruction *from, Instruction *to) -> bool {
                    if (!from) return false;
                    for (Instruction *it = from->getNextNode(); it && it != to; it = it->getNextNode()) {
                        if (it->mayWriteToMemory()) return true;
                    }
                    return false;
                };

                // Loop through each instruction of the basic block
                for (Instruction *Inst : originalInstructions) {
                    instCounter++;
                    if (!pendingLoadClones.empty() && writeBetween(prevInst, Inst)) {
                        flushLoadClones(lastLoadInst);
                        lastLoadInst = nullptr;
                    }
                    prevInst = Inst;
                    IRBuilder<> builder(Inst);
                    std::vector<Value*> clonedOperands;
                    std::vector<Value*> dependencyOperands;

                    Instruction *clonedInst = nullptr;
                    std::vector<Instruction*> clonedInsts;

                    // Duplicate Stores
                    if (isa<StoreInst>(Inst)) {
                        if (!pendingLoadClones.empty()) {
                            flushLoadClones(lastLoadInst);
                            lastLoadInst = nullptr;
                        }
                        IRBuilder<> storeBuilder(BB);
                        storeBuilder.SetInsertPoint(Inst->getNextNode());
                        Value *storedValue = Inst->getOperand(0);
                        Value *storeAddress = Inst->getOperand(1);

                        // Corner cases
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
                        // Type *storedType = storeAddress->getType()->getPointerElementType();
                        // if (storedType != storedValue->getType()) {
                        //     errs() << "Pointer element type does not match stored value type: "
                        //     << *storedType << " vs " << *storedValue->getType() << "\n";
                        //     continue;
                        // }

                        // Create a volatile load after the store
                        // LoadInst *reloadedValue = storeBuilder.CreateLoad(storeAddress->getType()->getPointerElementType(), storeAddress, true);
                        LoadInst *reloadedValue = storeBuilder.CreateLoad(storedValue->getType(), storeAddress, true);
                        reloadedValue->setAlignment(dyn_cast<StoreInst>(Inst)->getAlign());
                        reloadedValue->setVolatile(true); // Make the load volatile
                        clonedInst = reloadedValue;
                        originalValues[instCounter - 1] = storedValue;
                        InstToValueMap[Inst] = storedValue;

                        // Memory diversity
                        IRBuilder<> fenceBuilder(BB);
                        fenceBuilder.SetInsertPoint(reloadedValue->getNextNode());
                        InlineAsm *mfenceAsm = InlineAsm::get(FunctionType::get(Type::getVoidTy(F.getContext()), false), "mfence", "", true);
                        fenceBuilder.CreateCall(mfenceAsm);

                        // Second volatile load after the mfence
                        LoadInst *reloadedValue2 = fenceBuilder.CreateLoad(storedValue->getType(), storeAddress, true);
                        reloadedValue2->setAlignment(dyn_cast<StoreInst>(Inst)->getAlign());
                        reloadedValue2->setVolatile(true);

                        // clflush after the second volatile load
                        IRBuilder<> clflushBuilder(BB);
                        clflushBuilder.SetInsertPoint(reloadedValue2->getNextNode());
                        InlineAsm *clflushAsm = InlineAsm::get(FunctionType::get(Type::getVoidTy(F.getContext()), storeAddress->getType(), false), "clflush $0", "m", true);
                        clflushBuilder.CreateCall(clflushAsm, storeAddress);

                        // Third volatile load after the clflush
                        LoadInst *reloadedValue3 = clflushBuilder.CreateLoad(storedValue->getType(), storeAddress, true);
                        reloadedValue3->setAlignment(dyn_cast<StoreInst>(Inst)->getAlign());
                        reloadedValue3->setVolatile(true);

                        // Three reloads -> three comparisons against the stored value
                        clonedInsts.push_back(reloadedValue);
                        clonedInsts.push_back(reloadedValue2);
                        clonedInsts.push_back(reloadedValue3);

                    } else {
                        clonedInst = Inst->clone();

                        if (isa<LoadInst>(Inst)) {
                            LoadInst *loadInst = dyn_cast<LoadInst>(Inst);
                            LoadInst *clonedLoadInst = dyn_cast<LoadInst>(clonedInst);
                            clonedLoadInst->setAlignment(loadInst->getAlign());
                            clonedLoadInst->setVolatile(true); // Make the duplicate load volatile
                            clonedInst = clonedLoadInst;
                        }

                        // Maintain dependencies
                        for (unsigned i = 0; i < Inst->getNumOperands(); ++i) {
                            Value *operand = Inst->getOperand(i);
                            if (cloneMap.find(dyn_cast<Instruction>(operand)) != cloneMap.end()) {
                                // If there's a duplicate instruction for the operand, use that
                                auto &clonedOperandInsts = cloneMap[dyn_cast<Instruction>(operand)];
                                if (!clonedOperandInsts.empty()) {
                                    // Push the first cloned instruction into dependencyOperands
                                    dependencyOperands.push_back(clonedOperandInsts[0]);
                                }
                            } else {
                                dependencyOperands.push_back(operand);
                            }
                        }
                        for (size_t j = 0; j < dependencyOperands.size(); ++j) {
                                clonedInst->setOperand(j, dependencyOperands[j]);
                        }

                        // Aliasing protection
                        Value *loadPtr = dyn_cast<LoadInst>(Inst)->getPointerOperand();
                        pendingLoadClones.push_back({clonedInst, loadPtr});
                        lastLoadInst = Inst;
                        if ((int)pendingLoadClones.size() >= maxLoadBatch) {
                            flushLoadClones(Inst);
                            lastLoadInst = nullptr;
                        }

                        // Add the cloned instruction to clonedInsts
                        clonedInsts.push_back(clonedInst);
                    }

                    if (!clonedInsts.empty()) {
                        for (size_t ci = 0; ci < clonedInsts.size(); ++ci) {
                            cloneMap[Inst].push_back(clonedInsts[ci]);
                            clonedLastInst = clonedInsts[ci];

                            Value *lastValue = nullptr;
                            lastInst = originalInstructions[instCounter - 1];

                            if (isa<StoreInst>(Inst)) {
                                lastValue = originalValues[instCounter - 1];
                            }

                            if ((blockSize == 0 && (std::find(independentClusters.begin(), independentClusters.end(), lastInst) != independentClusters.end()))
                            || (blockSize != 0 && (instCounter % blockSize == 0 || instCounter == originalInstructions.size()))) {

                                if (cloneMap.find(lastInst) == cloneMap.end()) {
                                    errs() << "Error: No instruction in cloneMap!" << "\n";
                                }

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
                                    icmpResults.push_back(std::make_tuple(cmp, lastInst, clonedLastInst));
                                }
                            }
                        }
                    }
                }

                // Aliasing protection
                if (!pendingLoadClones.empty() && lastLoadInst) {
                    flushLoadClones(lastLoadInst);
                    lastLoadInst = nullptr;
                }

                // Create the comparison by aggregating the results of all icmp instructions and create the corresponding then/else blocks
                if (!icmpResults.empty()) {
                    IRBuilder<> aggCmpBuilder(BB->getTerminator());
                    Value *aggregateCmp = nullptr;

                    if (icmpResults.size() == 1) {
                        aggregateCmp = std::get<0>(icmpResults[0]);
                    } else {
                        aggregateCmp = aggCmpBuilder.CreateAnd(std::get<0>(icmpResults[0]), std::get<0>(icmpResults[1]), "init_agg_cmp");
                        for (unsigned i = 2; i < icmpResults.size(); ++i) {
                            aggregateCmp = aggCmpBuilder.CreateAnd(aggregateCmp, std::get<0>(icmpResults[i]), "agg_cmp");
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

                    for (auto &icmpTuple  : icmpResults) {
                        Value *cmpValue = std::get<0>(icmpTuple);
                        Instruction *origInstr = std::get<1>(icmpTuple);
                        Instruction *clonedInstr = std::get<2>(icmpTuple);
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

                        Type * instReturnType1 = nullptr;
                        if (origValue) {
                            instReturnType1 = origValue->getType();
                        } else {
                            instReturnType1 = origInstr->getType();
                        }

                        Type * instReturnType2 = clonedInstr->getType();

                        Value * formatStr = elseBuilder.CreateGlobalStringPtr("Potential Failing Instruction: %s \n");
                        Value * newLine = elseBuilder.CreateGlobalStringPtr("\n");

                        // Create the values for the memset call parameters
                        Value *Zero = elseBuilder.getInt8(0);

                        // Scratch buffers for the hex dump, sized to hold each value (min 64 bytes)
                        const DataLayout &DL = F.getParent()->getDataLayout();
                        uint64_t bufBytes1 = DL.getTypeStoreSize(instReturnType1);
                        uint64_t bufBytes2 = DL.getTypeStoreSize(instReturnType2);
                        if (bufBytes1 < 64) bufBytes1 = 64;
                        if (bufBytes2 < 64) bufBytes2 = 64;
                        Align bufAlign1 = DL.getABITypeAlign(instReturnType1);
                        Align bufAlign2 = DL.getABITypeAlign(instReturnType2);
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
                        // FunctionCallee incr_err = F.getParent()->getOrInsertFunction("incr_err", Type::getInt32PtrTy(Ctx), Type::getInt32Ty(Ctx), Type::getInt32Ty(Ctx));

                        Value * size_bytes1 = ConstantInt::get(Type::getInt32Ty(Ctx), size1, false);
                        Value * size_bytes2 = ConstantInt::get(Type::getInt32Ty(Ctx), size2, false);

                        Value * bb_index = ConstantInt::get(Type::getInt32Ty(Ctx), blockCounter, false);
                        Value * bb_total = ConstantInt::get(Type::getInt32Ty(Ctx), totalBasicBlocks, false);

                        // elseBuilder.CreateCall(incr_err, {bb_index, bb_total});
                        elseBuilder.CreateCall(fprintFunc, {formatStr, instName});
                        elseBuilder.CreateCall(pp, {castedAddr1, size_bytes1, castedAddr2, size_bytes2});
                        elseBuilder.CreateCall(fprintFunc, {newLine});
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

unsigned MemDivPass::blockCounter = 1;
unsigned MemDivPass::totalBasicBlocks = 0;
bool MemDivPass::countedBlocks = false;
unsigned MemDivPass::totalFunctions = 0;

char MemDivPass::ID = 0;

static RegisterPass<MemDivPass> X("memdivpass", "Insert memdiv pass", false, false);

static void registerMemDivPass(const PassManagerBuilder & Builder, legacy::PassManagerBase &PM) {
    PM.add(new MemDivPass());
}
static RegisterStandardPasses RegisterMemDivPass(PassManagerBuilder::EP_OptimizerLast, registerMemDivPass);
