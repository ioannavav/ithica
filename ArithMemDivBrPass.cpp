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
#include <vector>
#include <map>
#include <set>

using namespace llvm;

#ifndef BLOCKSIZE
#define BLOCKSIZE 1
#endif
#ifndef INTERLEAVING
#define INTERLEAVING 1
#endif
#ifndef LIBRARYNAME
#define LIBRARYNAME "top-level code"
#endif

namespace {

struct ArithMemDivBrPass : public FunctionPass {
  static char ID;

  static unsigned blockCounter;       
  static unsigned globalBlockCounter; 
  static unsigned totalBasicBlocks;
  static bool countedBlocks;

  ArithMemDivBrPass() : FunctionPass(ID) {}

  std::string instructionToString(Instruction *I) {
    if (!I) return "<null>";
    std::string str;
    raw_string_ostream rso(str);
    I->print(rso);
    rso.flush();
    std::string safeStr;
    for (char c : rso.str()) {
      if (c == '%')
        safeStr += "%_";
      else
        safeStr += c;
    }
    return safeStr;
  }

  bool isExcludedInstructionArithMem(Instruction *inst) {
    if (isa<InsertElementInst>(inst) || isa<AllocaInst>(inst) ||
        isa<AtomicCmpXchgInst>(inst) || isa<LandingPadInst>(inst) ||
        isa<InsertValueInst>(inst) || isa<FenceInst>(inst) ||
        isa<PHINode>(inst) || isa<AtomicRMWInst>(inst))
      return true;

    if (auto *ld = dyn_cast<LoadInst>(inst)) {
      if (ld->isAtomic() || ld->isVolatile())
        return true;
    }
    if (auto *st = dyn_cast<StoreInst>(inst)) {
      if (st->isAtomic() || st->isVolatile())
        return true;
    }
    if (auto *callInst = dyn_cast<CallInst>(inst)) {
      if (callInst->mayHaveSideEffects())
        return true;
      if (callInst->isInlineAsm()) {
        InlineAsm *inlineAsm = dyn_cast<InlineAsm>(callInst->getCalledOperand());
        if (inlineAsm &&
            inlineAsm->getAsmString().find("syscall") != std::string::npos) {
          return true;
        }
        return false; 
      }
      if (auto *calledF = callInst->getCalledFunction()) {
        if (calledF->getName().contains("llvm.") &&
            !callInst->getType()->isVoidTy()) {
          if (calledF->hasFnAttribute(Attribute::ReadOnly) ||
              calledF->hasFnAttribute(Attribute::ReadNone)) {
            return false;
          }
        }
      }
      if (callInst->getType()->isVoidTy())
        return true;
      return true;
    }
    return false;
  }


  bool isExcludedInstructionBranch(Instruction *inst) {
    if (auto *BI = dyn_cast<BranchInst>(inst)) {
      if (BI->isConditional()) {
        return false; // do not exclude conditional branches
      }
    }
    return true; // everything else is excluded
  }

  // Exclude “then*/else*” blocks to avoid re-instrument.

  bool isThenElseBlock(BasicBlock &BB) {
    StringRef name = BB.getName();
    return (name.startswith("then") || name.startswith("else"));
  }

  bool containsResumeOrCleanupInstruction(BasicBlock &BB) {
    for (Instruction &I : BB) {
      if (isa<ResumeInst>(I) || isa<LandingPadInst>(I))
        return true;
    }
    return false;
  }


  Value* handleOperandVolatile(Value *operand,
                               Function &F,
                               IRBuilder<> &builder,
                               IRBuilder<> &allocaBuilder) {
    if (isa<Constant>(operand)) {
      return operand;
    }
    if (isa<GetElementPtrInst>(operand)) {
      return operand;
    }
    // Create an alloca in function entry, store operand, load it back volatile.
    BasicBlock &entry = F.getEntryBlock();
    allocaBuilder.SetInsertPoint(&entry, entry.getFirstInsertionPt());

    AllocaInst *alloca = allocaBuilder.CreateAlloca(operand->getType(), nullptr,
                                                    "volatile_alloca");
    
    StoreInst *st = builder.CreateStore(operand, alloca);
    st->setVolatile(true);

    LoadInst *ld = builder.CreateLoad(alloca->getAllocatedType(), alloca);
    ld->setVolatile(true);
    return ld;
  }


  bool isExcludedFunctionArithMem(Function *F) {
    static const std::set<std::string> ExcludedFuncs = {
        "Function_name_to_exclude"
    };
    for (auto &str : ExcludedFuncs) {
      if (F->getName().str().find(str) != std::string::npos)
        return true;
    }
    return false;
  }


  bool isExcludedFunctionBranch(Function *F) {
    static const std::set<std::string> ExcludedFuncs = {
      //"ossl_lh_strcasehash",
      //"OPENSSL_LH_insert",
      //"CRYPTO_set_ex_data",
      //"ossl_sa_set",
      //"CRYPTO_zalloc",
      //"OPENSSL_LH_doall_arg",
      //"obj_name_cmp",
      //"_ZN8tcmalloc17tcmalloc_internal",
      //"SymbolizeEPK"
    };
    for (auto &str : ExcludedFuncs) {
      if (F->getName().str().find(str) != std::string::npos)
        return true;
    }
    return false;
  }

  void insertIDCheck(LLVMContext &Ctx,
                     BasicBlock *BB,
                     unsigned blockID,
                     GlobalVariable *branchTargetAddress,
                     GlobalVariable *branchCheckingON,
                     FunctionCallee fprintFunc,
                     FunctionCallee printCPUFunc,
                     FunctionCallee printDateFunc,
                     FunctionCallee exitFunc,
                     const char *libraryName,
                     Function &F,
                     std::set<BasicBlock*> &blocksWithCheck) {

    // Don’t double-instrument the same block
    if (blocksWithCheck.find(BB) != blocksWithCheck.end()) {
      return;
    }
    blocksWithCheck.insert(BB);

    Instruction *firstInst = BB->getFirstNonPHI();
    if (!firstInst) return;

    IRBuilder<> builder(firstInst);
    // Load the "branchCheckingON"
    Value *checkingOn = builder.CreateLoad(Type::getInt1Ty(Ctx), branchCheckingON, true);

    // Split the block
    BasicBlock *origBB = BB->splitBasicBlock(firstInst, "origBB");
    BasicBlock *checkBB = BasicBlock::Create(Ctx, "checkBB", &F);
    BasicBlock *skipBB  = BasicBlock::Create(Ctx, "skipCheckBB", &F);

    builder.SetInsertPoint(BB->getTerminator());
    builder.CreateCondBr(checkingOn, checkBB, skipBB);
    BB->getTerminator()->eraseFromParent();

    // checkBB => compare stored ID with current block ID
    IRBuilder<> checkBuilder(checkBB);
    Value *storedID = checkBuilder.CreateLoad(Type::getInt32Ty(Ctx),
                                              branchTargetAddress, true);
    Value *currentID = ConstantInt::get(Type::getInt32Ty(Ctx), blockID);
    Value *isCorrect = checkBuilder.CreateICmpEQ(storedID, currentID);

    BasicBlock *thenBB  = BasicBlock::Create(Ctx, "thenBB", &F);
    BasicBlock *errorBB = BasicBlock::Create(Ctx, "errorBB", &F);

    checkBuilder.CreateCondBr(isCorrect, thenBB, errorBB);

    // thenBB => turn OFF checking, jump to origBB
    IRBuilder<> thenBuilder(thenBB);
    thenBuilder.CreateStore(ConstantInt::get(Type::getInt1Ty(Ctx), true),
                            branchCheckingON);
    thenBuilder.CreateBr(origBB);

    // errorBB => mismatch => do prints + call exit(-1), unreachable
    IRBuilder<> errBuilder(errorBB);
    // Print info
    Value *funcName = errBuilder.CreateGlobalStringPtr(F.getName());
    Value *blockIdVal = ConstantInt::get(Type::getInt32Ty(Ctx), blockID);
    Value *msg = errBuilder.CreateGlobalStringPtr(
       "Error in function: %s , #Basic block: %d , Mismatched branch target!\n");

    errBuilder.CreateCall(fprintFunc, {msg, funcName, blockIdVal});
    errBuilder.CreateCall(printCPUFunc);

    Value* libraryNameArg = errBuilder.CreateGlobalStringPtr(libraryName);
    Value* prefix = errBuilder.CreateGlobalStringPtr("Error occurred on: ");
    errBuilder.CreateCall(fprintFunc, prefix);
    errBuilder.CreateCall(printDateFunc, libraryNameArg);

    errBuilder.CreateCall(exitFunc, ConstantInt::get(Type::getInt32Ty(Ctx), -1));
    errBuilder.CreateUnreachable();

    IRBuilder<> skipBuilder(skipBB);
    skipBuilder.CreateBr(origBB);
  }

  // Count all BBs in the module (only once).
  static void countAllBasicBlocks(Module *M) {
    unsigned count = 0;
    for (Function &F : *M) {
      if (!F.isDeclaration()) {
        count += std::distance(F.begin(), F.end());
      }
    }
    totalBasicBlocks = count;
    errs() << "Total basic blocks in module: " << totalBasicBlocks << "\n";
  }


  bool runOnFunction(Function &F) override {
    if (isExcludedFunctionArithMem(&F) || isExcludedFunctionBranch(&F)) {
      // If the function is excluded by either sub-pass, skip
      return false;
    }

    Module *M = F.getParent();
    LLVMContext &Ctx = M->getContext();

    // If this is our first time, count total BBs once
    if (!countedBlocks) {
      countAllBasicBlocks(M);
      countedBlocks = true;
    }

    // We retrieve or insert these helper calls for both passes:
    FunctionCallee fprintFunc = M->getOrInsertFunction(
      "fprintFunc",
      FunctionType::get(IntegerType::getInt32Ty(Ctx),
                        PointerType::get(Type::getInt8Ty(Ctx), 0))
    );

    FunctionCallee printCPUFunc = M->getOrInsertFunction(
      "print_cpu_id",
      FunctionType::get(Type::getVoidTy(Ctx), false)
    );

    FunctionCallee printDateFunc = M->getOrInsertFunction(
      "print_date",
      FunctionType::get(Type::getVoidTy(Ctx),
                        Type::getInt8PtrTy(Ctx),
                        false)
    );

    // Also for the "exit(-1)" usage:
    FunctionCallee exitFunc = M->getOrInsertFunction(
      "exit",
      FunctionType::get(Type::getVoidTy(Ctx),
                        Type::getInt32Ty(Ctx),
                        false)
    );

    // ARITH/MEM PART
    {
     
      int blockSize = BLOCKSIZE;
      int interleaving = INTERLEAVING;
      const char *libraryName = LIBRARYNAME;

      // Gather original BBs
      std::vector<BasicBlock*> bbs;
      for (auto &BB : F) {
        bbs.push_back(&BB);
      }

      // For each BB, clone instructions except the excluded
      for (auto *BB : bbs) {
        if (isThenElseBlock(*BB)) continue;
        if (containsResumeOrCleanupInstruction(*BB)) continue;

        std::vector<Instruction*> originalInsts;
        std::vector<Value*>       originalVals;
        std::map<Instruction*, std::vector<Instruction*>> dependencyGraph;

        // Collect instructions
        for (Instruction &I : *BB) {
          if (&I != BB->getTerminator() && !isExcludedInstructionArithMem(&I)) {
            originalInsts.push_back(&I);
            originalVals.push_back(&I);

            // Build dependency info
            std::vector<Instruction*> deps;
            for (Use &U : I.operands()) {
              if (auto *depI = dyn_cast<Instruction>(U.get())) {
                deps.push_back(depI);
              }
            }
            dependencyGraph[&I] = deps;
          }
        }

        // Identify "independent cluster" instructions
        std::vector<Instruction*> independentClusters;
        for (auto &kv : dependencyGraph) {
          Instruction *inst = kv.first;
          bool isEndOfCluster = true;
          for (auto &kv2 : dependencyGraph) {
            auto &depVec = kv2.second;
            if (std::find(depVec.begin(), depVec.end(), inst) != depVec.end()) {
              isEndOfCluster = false;
              break;
            }
          }
          if (isEndOfCluster) {
            independentClusters.push_back(inst);
          }
        }

        // Maps from original->clones
        std::map<Instruction*, std::vector<Instruction*>> cloneMap;
        std::map<Instruction*, Value*> InstToValueMap;
        std::vector<std::pair<Value*, Instruction*>> icmpResults;

        // IRBuilder for alloca insertion in the function's entry
        IRBuilder<> allocaBuilder(Ctx);
        allocaBuilder.SetInsertPoint(&*F.getEntryBlock().getFirstInsertionPt());

        unsigned instCount = 0;
        for (auto *Inst : originalInsts) {
          instCount++;
          IRBuilder<> builder(Inst);

          Instruction *clonedInst = nullptr;
          std::vector<Instruction*> clonedInsts;

          // Check if store
          if (auto *st = dyn_cast<StoreInst>(Inst)) {
            // We do the store reload trick, plus fences, etc.
            IRBuilder<> storeBuilder(Inst->getNextNode());
            Value *valToStore = st->getValueOperand();
            Value *storeAddr  = st->getPointerOperand();

            // Basic corner checks
            if (!storeAddr->getType()->isPointerTy()) continue;
            if (isa<ConstantPointerNull>(storeAddr))  continue;
            Type *pointeeTy = storeAddr->getType()->getPointerElementType();
            if (pointeeTy != valToStore->getType())    continue;

            LoadInst *reloaded1 = storeBuilder.CreateLoad(pointeeTy, storeAddr, "reload1");
            reloaded1->setVolatile(true);
            reloaded1->setAlignment(st->getAlign());

            clonedInst = reloaded1;
            InstToValueMap[Inst] = valToStore;

            // Insert mfence
            IRBuilder<> fenceBuilder(reloaded1->getNextNode());
            InlineAsm *mfenceAsm = InlineAsm::get(
               FunctionType::get(Type::getVoidTy(Ctx), false),
               "mfence", "", true);
            fenceBuilder.CreateCall(mfenceAsm);

            // reloaded2
            LoadInst *reloaded2 = fenceBuilder.CreateLoad(pointeeTy, storeAddr, "reload2");
            reloaded2->setAlignment(st->getAlign());
            reloaded2->setVolatile(true);

            // clflush
            IRBuilder<> flushBuilder(reloaded2->getNextNode());
            InlineAsm *clflushAsm = InlineAsm::get(
               FunctionType::get(Type::getVoidTy(Ctx), storeAddr->getType(), false),
               "clflush $0", "m", true);
            flushBuilder.CreateCall(clflushAsm, storeAddr);

            // reloaded3
            LoadInst *reloaded3 = flushBuilder.CreateLoad(pointeeTy, storeAddr, "reload3");
            reloaded3->setAlignment(st->getAlign());
            reloaded3->setVolatile(true);

            clonedInsts.push_back(reloaded1);
            clonedInsts.push_back(reloaded2);
            clonedInsts.push_back(reloaded3);
          }
          else {
            // Clone the instruction
            clonedInst = Inst->clone();
            // If it’s a load, set alignment and volatility
            if (auto *ld = dyn_cast<LoadInst>(Inst)) {
              auto *clonedLd = dyn_cast<LoadInst>(clonedInst);
              if (clonedLd) {
                clonedLd->setAlignment(ld->getAlign());
                clonedLd->setVolatile(true);
              }
            }

            // Maintain dependencies
            std::vector<Value*> newOperands;
            for (unsigned i=0; i<Inst->getNumOperands(); i++) {
              Value *op = Inst->getOperand(i);
              // If op is itself cloned, use that:
              if (auto *depI = dyn_cast<Instruction>(op)) {
                if (cloneMap.find(depI) != cloneMap.end()) {
                  auto &cvec = cloneMap[depI];
                  if (!cvec.empty()) {
                    newOperands.push_back(cvec[0]);
                    continue;
                  }
                }
              }
              newOperands.push_back(op);
            }
            // Volatile
            std::vector<Value*> finalOps;
            bool replacedAny = false;
            for (auto *op : newOperands) {
              if (isa<Constant>(op)) {
                finalOps.push_back(op);
              }
              else {
                replacedAny = true;
                Value *volOp = handleOperandVolatile(op, F, builder, allocaBuilder);
                finalOps.push_back(volOp);
              }
            }

            for (size_t j=0; j<finalOps.size(); j++) {
              clonedInst->setOperand(j, finalOps[j]);
            }

            // Insert the clone
            if (interleaving == 1 || isa<LoadInst>(Inst)) {
              clonedInst->insertAfter(Inst);
            } else {
              clonedInst->insertBefore(BB->getTerminator());
            }

            // Memory diversity for loads: clflush after
            if (auto *ld = dyn_cast<LoadInst>(Inst)) {
              IRBuilder<> flushBuilder(Inst->getNextNode());
              Value *ptr = ld->getPointerOperand();
              InlineAsm *clflushAsm = InlineAsm::get(
                  FunctionType::get(Type::getVoidTy(Ctx), ptr->getType(), false),
                  "clflush $0", "m", true);
              flushBuilder.CreateCall(clflushAsm, ptr);
            }
            clonedInsts.push_back(clonedInst);
          }

          if (!clonedInsts.empty()) {
            for (auto *ci : clonedInsts) {
              cloneMap[Inst].push_back(ci);

              Instruction *lastOrig = originalInsts[instCount-1];
              Value *lastValue = nullptr;
              if (isa<StoreInst>(Inst)) {
                lastValue = originalVals[instCount-1];
              }
              // Condition for comparing now:
              bool doCompare = false;
              // blockSize==0 => compare if "independent cluster" 
              // else compare if we've reached the blockSize boundary or end
              if (blockSize == 0) {
                if (std::find(independentClusters.begin(), independentClusters.end(),
                              lastOrig) != independentClusters.end()) {
                  doCompare = true;
                }
              } else {
                if ((instCount % blockSize == 0) ||
                    (instCount == originalInsts.size())) {
                  doCompare = true;
                }
              }

              if (doCompare) {
                IRBuilder<> b2(BB->getTerminator());
                Value *cmp = nullptr;
                Instruction *clonedLast = ci;

                if (lastValue) {
                  if (lastValue->getType()->isIntegerTy() &&
                      clonedLast->getType()->isIntegerTy()) {
                    cmp = b2.CreateICmpEQ(lastValue, clonedLast, "cmp_result");
                  } else if (lastValue->getType()->isFloatingPointTy() &&
                             clonedLast->getType()->isFloatingPointTy()) {
                    cmp = b2.CreateFCmpOEQ(lastValue, clonedLast, "cmp_result");
                  }
                  // handle vectors/pointers if needed
                }
                else {
                  // Compare lastOrig->getType() with clonedLast->getType()
                  if (lastOrig->getType()->isIntegerTy() &&
                      clonedLast->getType()->isIntegerTy()) {
                    cmp = b2.CreateICmpEQ(lastOrig, clonedLast, "cmp_result");
                  } else if (lastOrig->getType()->isFloatingPointTy() &&
                             clonedLast->getType()->isFloatingPointTy()) {
                    cmp = b2.CreateFCmpOEQ(lastOrig, clonedLast, "cmp_result");
                  }
                }
                if (cmp) {
                  icmpResults.push_back(std::make_pair(cmp, lastOrig));
                }
              }
            }
          }
        } 

        if (!icmpResults.empty()) {
          IRBuilder<> aggBuilder(BB->getTerminator());
          Value *aggCmp = nullptr;
          if (icmpResults.size() == 1) {
            aggCmp = icmpResults[0].first;
          } else {
            aggCmp = aggBuilder.CreateAnd(icmpResults[0].first,
                                          icmpResults[1].first,
                                          "init_cmp");
            for (unsigned i=2; i<icmpResults.size(); i++) {
              aggCmp = aggBuilder.CreateAnd(aggCmp, icmpResults[i].first,
                                            "agg_cmp");
            }
          }

          BasicBlock *thenBB = BB->splitBasicBlock(aggBuilder.GetInsertPoint(),
                             "thenBlock");
          BasicBlock *elseBB = BasicBlock::Create(Ctx,
                             "elseBlock",
                             &F, thenBB);

          BB->getTerminator()->eraseFromParent();
          aggBuilder.SetInsertPoint(BB);
          aggBuilder.CreateCondBr(aggCmp, thenBB, elseBB);

          // In elseBB => print & jump back
          IRBuilder<> elseB(elseBB);
          elseB.CreateCall(printCPUFunc);
          Value *libNameArg = elseB.CreateGlobalStringPtr(LIBRARYNAME);
          elseB.CreateCall(printDateFunc, libNameArg);

          Value *fname = elseB.CreateGlobalStringPtr(F.getName());
          Value *bId = ConstantInt::get(Type::getInt32Ty(Ctx), blockCounter);
          Value *fmt = elseB.CreateGlobalStringPtr("Error in function: %s , #Basic block: %d \n\0");
          elseB.CreateCall(fprintFunc, {fmt, fname, bId});

          for (auto &p : icmpResults) {
            Instruction *origI = p.second;
            std::string s = instructionToString(origI);
            Value *msg = elseB.CreateGlobalStringPtr(s);
            Value *fmt2 = elseB.CreateGlobalStringPtr("Potential Failing Instruction: %s\n");
            elseB.CreateCall(fprintFunc, {fmt2, msg});
          }

          std::string sepBeg = "-------------- Beginning Of Failing Block ------------\n";
          Value *sepBVal = elseB.CreateGlobalStringPtr(sepBeg);
          elseB.CreateCall(fprintFunc, {sepBVal});
          for (Instruction &I : *BB) {
            std::string iStr = instructionToString(&I)+"\n";
            Value *val = elseB.CreateGlobalStringPtr(iStr);
            elseB.CreateCall(fprintFunc, {val});
          }
          std::string sepEnd = "**************** End Of Failing Block *****************\n\n";
          Value *sepEVal = elseB.CreateGlobalStringPtr(sepEnd);
          elseB.CreateCall(fprintFunc, {sepEVal});

          // Just branch to thenBB
          elseB.CreateBr(thenBB);
        }

        blockCounter++;
      } // end for each BB (arithmem part)
    }

    // BRANCH PART
    {
      // We need the global variables for branch instrumentation
      GlobalVariable *branchTargetAddress = M->getNamedGlobal("llvmPassBranchTargetAddress");
      if (!branchTargetAddress) {
        branchTargetAddress = new GlobalVariable(
          *M,
          Type::getInt32Ty(Ctx),
          false, // isConstant
          GlobalValue::InternalLinkage,
          ConstantInt::get(Type::getInt32Ty(Ctx), 0),
          "llvmPassBranchTargetAddress"
        );
        branchTargetAddress->setThreadLocal(true);
      }
      GlobalVariable *branchCheckingON = M->getNamedGlobal("llvmPassBranchCheckingON");
      if (!branchCheckingON) {
        branchCheckingON = new GlobalVariable(
          *M,
          Type::getInt1Ty(Ctx),
          false,
          GlobalValue::InternalLinkage,
          ConstantInt::get(Type::getInt1Ty(Ctx), false),
          "llvmPassBranchCheckingON"
        );
        branchCheckingON->setThreadLocal(true);
      }

      // Assign a global ID to each basic block
      std::map<BasicBlock*, unsigned> blockIDMap;
      std::vector<BasicBlock*> allBBs;
      for (auto &BB : F) {
        allBBs.push_back(&BB);
      }
      for (auto *BB : allBBs) {
        blockIDMap[BB] = globalBlockCounter++;
      }

      // We'll store the conditional branches in each BB
      std::map<BasicBlock*, std::vector<Instruction*>> blockBranchMap;
      for (auto *BB : allBBs) {
        if (isThenElseBlock(*BB)) continue;
        if (containsResumeOrCleanupInstruction(*BB)) continue;
        std::vector<Instruction*> brs;
        for (Instruction &I : *BB) {
          if (!isExcludedInstructionBranch(&I)) {
            brs.push_back(&I);
          }
        }
        blockBranchMap[BB] = brs;
      }

      // Keep track of blocks we inserted “ID check” into
      std::set<BasicBlock*> blocksWithCheck;

      for (auto *BB : allBBs) {
        for (auto *Inst : blockBranchMap[BB]) {
          if (auto *branchInst = dyn_cast<BranchInst>(Inst)) {
            if (branchInst->isConditional()) {
              BasicBlock *trueBB  = branchInst->getSuccessor(0);
              BasicBlock *falseBB = branchInst->getSuccessor(1);

              // Insert code: store ID of expected block
              IRBuilder<> bld(branchInst);
              Value *trueID  = ConstantInt::get(Type::getInt32Ty(Ctx),
                                                blockIDMap[trueBB]);
              Value *falseID = ConstantInt::get(Type::getInt32Ty(Ctx),
                                                blockIDMap[falseBB]);
              Value *cond = branchInst->getCondition();
              Value *expectedID = bld.CreateSelect(cond, trueID, falseID);
              bld.CreateStore(expectedID, branchTargetAddress, true);
              bld.CreateStore(ConstantInt::get(Type::getInt1Ty(Ctx), true),
                              branchCheckingON);

              // Now insert the ID check in the target blocks
              insertIDCheck(Ctx, trueBB,  blockIDMap[trueBB],
                            branchTargetAddress, branchCheckingON,
                            fprintFunc, printCPUFunc, printDateFunc,
                            exitFunc, LIBRARYNAME, F, blocksWithCheck);
              insertIDCheck(Ctx, falseBB, blockIDMap[falseBB],
                            branchTargetAddress, branchCheckingON,
                            fprintFunc, printCPUFunc, printDateFunc,
                            exitFunc, LIBRARYNAME, F, blocksWithCheck);
            }
          }
        }
      }
    }

    return true;
  } 
};

} // end anonymous namespace

char ArithMemDivBrPass::ID = 0;
unsigned ArithMemDivBrPass::blockCounter       = 1;
unsigned ArithMemDivBrPass::globalBlockCounter = 1;
unsigned ArithMemDivBrPass::totalBasicBlocks   = 0;
bool     ArithMemDivBrPass::countedBlocks      = false;

static RegisterPass<ArithMemDivBrPass>
  X("arithmemdivbrpass", "Combined arithmetic/memory/branch instrumentation pass", false, false  
);

static void registerArithMemDivBrPass(const PassManagerBuilder &Builder,
                                      legacy::PassManagerBase &PM) {
  PM.add(new ArithMemDivBrPass());
}
static RegisterStandardPasses RegisterArithMemDivBr(
  PassManagerBuilder::EP_OptimizerLast, registerArithMemDivBrPass
);
