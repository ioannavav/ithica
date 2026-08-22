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
#include "llvm/IR/CallingConv.h"
#include "llvm/Support/ErrorHandling.h"
#include <iterator>
#include <vector>
#include <map>
#include <set>

using namespace llvm;
static std::map<unsigned, Function*> NoOpFunctionRegistry;

namespace {
    struct BranchPass : public FunctionPass {
        static char ID;
        BranchPass() : FunctionPass(ID) {}

        static unsigned blockCounter;       // Basic block ID within the function
        static unsigned globalBlockCounter; // Global unique block ID across all functions
        static unsigned totalBasicBlocks;   // Total number of basic blocks across functions
        static bool countedBlocks;          // Ensure basic blocks are counted only once
        static unsigned totalFunctions;

        std::string instructionToString(Instruction *I) {
            std::string str;
            llvm::raw_string_ostream rso(str);
            I->print(rso);
            rso.flush(); // Ensure the stream is flushed
            return rso.str();
        }

        // Exclude all instructions except conditional branches
        bool isExcludedInstruction(Instruction *inst) {
            if (BranchInst *branchInst = dyn_cast<BranchInst>(inst)) {
                if (branchInst->isConditional()) {
                    return false;  // Do not exclude conditional branch instructions
                }
            }
            return true; // Exclude all other instructions
        }

        bool containsResumeOrCleanupInstruction(BasicBlock &BB) {
            for (Instruction &I : BB) {
                if (isa<ResumeInst>(&I) || isa<LandingPadInst>(&I)) {
                    return true;
                }
            }
            return false;
        }

        // Exclude Then/Else blocks from processing. These are blocks added by instrumentation
        bool isThenElseBlock(BasicBlock &BB) {
            StringRef name = BB.getName();
            return name.startswith("then") || name.startswith("else");
        }

        // Exclude certain functions from being processed
        bool isExcludedFunction(Function *F) {
            static const std::set<std::string> ExcludedFunctions = {
                "ossl_lh_strcasehash", "OPENSSL_LH_insert", "CRYPTO_set_ex_data",
                "ossl_sa_set", "CRYPTO_zalloc", "OPENSSL_LH_doall_arg", "obj_name_cmp",
                "_ZN8tcmalloc17tcmalloc_internal", "SymbolizeEPK",
                "Add other functions to exclude"
            };
            for (const auto &excludedName : ExcludedFunctions) {
                if (F->getName().str().find(excludedName) != std::string::npos) {
                    return true;
                }
            }
            return false;
        }

        GlobalVariable *getOrCreateThreadLocalGlobal(Module *M, Type *ty, Constant *init, StringRef name) {
            GlobalVariable *gv = M->getNamedGlobal(name);
            if (!gv) {
                gv = new GlobalVariable(*M, ty, false, GlobalValue::InternalLinkage, init, name);
                gv->setThreadLocal(true);
            }
            return gv;
        }

        Function *getOrCreateCheckFn(Module *M, LLVMContext &Ctx,
                                     GlobalVariable *tgt, GlobalVariable *on,
                                     FunctionCallee fprintFunc, FunctionCallee printCPUFunc,
                                     FunctionCallee printDateFunc) {
            if (Function *f = M->getFunction("__ithica_branch_check")) return f;
            FunctionType *fty = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx)}, false);
            Function *f = Function::Create(fty, GlobalValue::InternalLinkage, "__ithica_branch_check", M);
            f->addFnAttr(Attribute::NoInline);
            f->setCallingConv(CallingConv::PreserveMost);
            Argument *blockID = f->getArg(0);
            BasicBlock *entry = BasicBlock::Create(Ctx, "entry", f);
            BasicBlock *fail = BasicBlock::Create(Ctx, "fail", f);
            BasicBlock *cont = BasicBlock::Create(Ctx, "cont", f);
            IRBuilder<> b(entry);
            Value *chk = b.CreateLoad(Type::getInt1Ty(Ctx), on, true);
            Value *storedID = b.CreateLoad(Type::getInt32Ty(Ctx), tgt, true);
            Value *mism = b.CreateICmpNE(storedID, blockID);
            Value *err = b.CreateAnd(chk, mism);
            b.CreateStore(ConstantInt::get(Type::getInt1Ty(Ctx), false), on, true);
            b.CreateCondBr(err, fail, cont);

            IRBuilder<> fb(fail);
            // Optional logging
            Value *fmt = fb.CreateGlobalStringPtr("Mismatched branch target! block %d\n");
            fb.CreateCall(fprintFunc, {fmt, blockID});
            fb.CreateCall(printCPUFunc);
            fb.CreateCall(printDateFunc, fb.CreateGlobalStringPtr(LIBRARYNAME));
            FunctionCallee fflushFunc = M->getOrInsertFunction(
                "fflush", FunctionType::get(Type::getInt32Ty(Ctx),
                PointerType::get(Type::getInt8Ty(Ctx), 0)));
            FunctionCallee abortFunc = M->getOrInsertFunction(
                "abort", FunctionType::get(Type::getVoidTy(Ctx), false));
            if (Function *ad = dyn_cast<Function>(abortFunc.getCallee())) ad->setDoesNotReturn();
            fb.CreateCall(fflushFunc, ConstantPointerNull::get(PointerType::get(Type::getInt8Ty(Ctx), 0)));
            fb.CreateCall(abortFunc);
            fb.CreateUnreachable();

            IRBuilder<> cb(cont);
            cb.CreateRetVoid();
            return f;
        }

        Function *getOrCreateSetFn(Module *M, LLVMContext &Ctx,
                                   GlobalVariable *tgt, GlobalVariable *on) {
            if (Function *f = M->getFunction("__ithica_branch_set")) return f;
            FunctionType *fty = FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt32Ty(Ctx)}, false);
            Function *f = Function::Create(fty, GlobalValue::InternalLinkage, "__ithica_branch_set", M);
            f->addFnAttr(Attribute::NoInline);
            f->setCallingConv(CallingConv::PreserveMost);
            Argument *expectedID = f->getArg(0);
            BasicBlock *entry = BasicBlock::Create(Ctx, "entry", f);
            IRBuilder<> b(entry);
            b.CreateStore(expectedID, tgt, true);
            b.CreateStore(ConstantInt::get(Type::getInt1Ty(Ctx), true), on, true);
            b.CreateRetVoid();
            return f;
        }

        void insertIDCheck(LLVMContext &Ctx, BasicBlock *BB, unsigned blockID,
                           Function *checkFn, std::set<BasicBlock*> &blocksWithCheck) {
            if (blocksWithCheck.find(BB) != blocksWithCheck.end()) return;
            blocksWithCheck.insert(BB);
            Instruction *firstInst = BB->getFirstNonPHI();
            if (!firstInst) return;
            IRBuilder<> builder(firstInst);
            CallInst *ci = builder.CreateCall(checkFn, {ConstantInt::get(Type::getInt32Ty(Ctx), blockID)});
            ci->setCallingConv(CallingConv::PreserveMost);
        }

        void instrumentConditionalBranch(BranchInst *condBranchInst, BasicBlock *BB,
                LLVMContext &Ctx, Function &F, std::map<BasicBlock*, unsigned> &blockIDMap,
                Function *checkFn, Function *setFn, std::set<BasicBlock*> &blocksWithCheck) {
            BasicBlock *trueTarget = condBranchInst->getSuccessor(0);
            BasicBlock *falseTarget = condBranchInst->getSuccessor(1);
            IRBuilder<> builder(condBranchInst);
            Value *trueTargetID = ConstantInt::get(Type::getInt32Ty(Ctx), blockIDMap[trueTarget]);
            Value *falseTargetID = ConstantInt::get(Type::getInt32Ty(Ctx), blockIDMap[falseTarget]);
            Value *expectedID = builder.CreateSelect(condBranchInst->getCondition(), trueTargetID, falseTargetID);
            CallInst *ci = builder.CreateCall(setFn, {expectedID});
            ci->setCallingConv(CallingConv::PreserveMost);
            insertIDCheck(Ctx, trueTarget, blockIDMap[trueTarget], checkFn, blocksWithCheck);
            insertIDCheck(Ctx, falseTarget, blockIDMap[falseTarget], checkFn, blocksWithCheck);
        }

        bool runOnFunction(Function &F) override {
            if (isExcludedFunction(&F)) {
                return false;
            }

            LLVMContext &Ctx = F.getContext();
            Module *M = F.getParent();
            totalFunctions++;
            errs() << " Running on function: " << F.getName() <<  "  with ID: " <<  totalFunctions << "\n";

            // Declare external functions used for printing and error handling
            FunctionCallee fprintFunc = M->getOrInsertFunction(
                "fprintFunc", FunctionType::get(IntegerType::getInt32Ty(Ctx),
                PointerType::get(Type::getInt8Ty(Ctx), 0)));
            FunctionCallee printCPUFunc = M->getOrInsertFunction(
                "print_cpu_id", FunctionType::get(Type::getVoidTy(Ctx), false));
            FunctionCallee printDateFunc = M->getOrInsertFunction(
                "print_date", FunctionType::get(Type::getVoidTy(Ctx), Type::getInt8PtrTy(Ctx), false));

            // Get or create the global variables for branch target address and branch checking ON
            GlobalVariable *branchTargetAddress = getOrCreateThreadLocalGlobal(
                M, Type::getInt32Ty(Ctx), ConstantInt::get(Type::getInt32Ty(Ctx), 0),
                "llvmPassBranchTargetAddress");
            GlobalVariable *branchCheckingON = getOrCreateThreadLocalGlobal(
                M, Type::getInt1Ty(Ctx), ConstantInt::get(Type::getInt1Ty(Ctx), false),
                "llvmPassBranchCheckingON");

            Function *checkFn = getOrCreateCheckFn(M, Ctx, branchTargetAddress, branchCheckingON,
                                                   fprintFunc, printCPUFunc, printDateFunc);
            Function *setFn = getOrCreateSetFn(M, Ctx, branchTargetAddress, branchCheckingON);

            if (&F == checkFn || &F == setFn) return true;

            std::vector<BasicBlock*> bbs;
            std::map<BasicBlock*, unsigned> blockIDMap;
            std::set<BasicBlock*> blocksWithCheck;
            std::map<BasicBlock*, std::vector<Instruction*>> blockInstructionMap;

            // Assign unique IDs to basic blocks and collect them
            for (BasicBlock &BB : F) {
                blockIDMap[&BB] = globalBlockCounter++;
            }

            // Collect each function's instrumentable instructions.
            for (Function::iterator BI = F.begin(), BE = F.end(); BI != BE; ++BI) {
                BasicBlock *BB = &*BI;
                bbs.push_back(BB);
                std::vector<Instruction*> originalInstructions;
                for (Instruction &I : *BB) {
                    if (!isExcludedInstruction(&I)) {
                        originalInstructions.push_back(&I);
                    }
                }
                blockInstructionMap[BB] = originalInstructions;
            }

            if (!countedBlocks) {
                countBasicBlocks(M);
                countedBlocks = true;
            }

            // Process each basic block
            for (auto BI : bbs) {
                BasicBlock *BB = BI;
                if (isThenElseBlock(*BB) || containsResumeOrCleanupInstruction(*BB)) {
                    continue;
                }
                // Loop through each instruction of the basic block
                for (Instruction *Inst : blockInstructionMap[BB]) {
                    BranchInst *condBranchInst = dyn_cast<BranchInst>(Inst);
                    if (condBranchInst && condBranchInst->isConditional()) {
                        instrumentConditionalBranch(condBranchInst, BB, Ctx, F, blockIDMap,
                                                    checkFn, setFn, blocksWithCheck);
                    }
                }
                blockCounter++;
            }
            return true;
        }

        // Function to count total basic blocks in the module
        static void countBasicBlocks(Module *M) {
            for (Function &F : *M) {
                if (!F.isDeclaration()) {
                    totalBasicBlocks += std::distance(F.begin(), F.end());
                }
            }
        }

    };
}

unsigned BranchPass::blockCounter = 1;
unsigned BranchPass::globalBlockCounter = 1;
unsigned BranchPass::totalBasicBlocks = 0;
bool BranchPass::countedBlocks = false;
unsigned BranchPass::totalFunctions = 0;

// Register the pass
char BranchPass::ID = 0;

static RegisterPass<BranchPass> X("branchpass", "Insert checks for conditional branch instructions", false, false);

static void registerBranchPass(const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new BranchPass());
}

static RegisterStandardPasses RegisterBranchPass(PassManagerBuilder::EP_OptimizerLast, registerBranchPass);
