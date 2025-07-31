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
    struct BranchPass : public FunctionPass {
        static char ID;
        BranchPass() : FunctionPass(ID) {}

        // Static variables to keep track of basic blocks and functions
        static unsigned blockCounter;       // Basic block ID within the function
        static unsigned globalBlockCounter; // Global unique block ID across all functions
        static unsigned totalBasicBlocks;   // Total number of basic blocks across functions
        static bool countedBlocks;          // Ensure basic blocks are counted only once

        // Helper function to convert an instruction to a string
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
                // Excluded functions to avoid false positives due to multithreading.
                "Function_to_exclude",
            };
            for (const auto &excludedName : ExcludedFunctions) {
                if (F->getName().str().find(excludedName) != std::string::npos) {
                    return true;
                }
            }
            return false;
        }

        // Function to insert ID check at the beginning of a basic block
        void insertIDCheck(
            LLVMContext &Ctx,
            BasicBlock *BB,
            unsigned blockID,
            GlobalVariable *branchTargetAddress,
            GlobalVariable *branchCheckingON,
            FunctionCallee fprintFunc,
            FunctionCallee printCPUFunc,
            FunctionCallee printDateFunc,
            Function &F,
            std::set<BasicBlock*> &blocksWithCheck) {

            // Check if the ID check has already been inserted for this block
            if (blocksWithCheck.find(BB) != blocksWithCheck.end()) {
                return;
            }
            blocksWithCheck.insert(BB);

            // Get the first non-PHI instruction in the block
            Instruction *firstInst = BB->getFirstNonPHI();
            if (!firstInst) {
                // No instructions to insert before
                return;
            }

            IRBuilder<> builder(firstInst);

            // Load the value of branchCheckingON
            Value *branchCheckEnabled = builder.CreateLoad(Type::getInt1Ty(Ctx), branchCheckingON);

            // Split the block at the first instruction, creating a new block for the instructions after the split
            BasicBlock *origBB = BB->splitBasicBlock(firstInst, "origBB");

            // Create new basic blocks for the check and skip paths
            BasicBlock *checkBB = BasicBlock::Create(Ctx, "checkBB", &F);
            BasicBlock *skipCheckBB = BasicBlock::Create(Ctx, "skipCheckBB", &F);

            // Replace the terminator of BB with a conditional branch based on branchCheckEnabled
            builder.SetInsertPoint(BB->getTerminator());
            builder.CreateCondBr(branchCheckEnabled, checkBB, skipCheckBB);
            BB->getTerminator()->eraseFromParent();  // Remove the old terminator

            // Build the checkBB block (this block will handle the ID checking)
            IRBuilder<> checkBuilder(checkBB);

            // Load the stored branch target ID
            Value *storedID = checkBuilder.CreateLoad(Type::getInt32Ty(Ctx), branchTargetAddress, true);

            // Compare it with the current block ID
            Value *currentBlockIDVal = ConstantInt::get(Type::getInt32Ty(Ctx), blockID);
            Value *isCorrectTarget = checkBuilder.CreateICmpEQ(storedID, currentBlockIDVal);

            // Create then and error blocks based on the comparison
            BasicBlock *thenBB = BasicBlock::Create(Ctx, "thenBB", &F);
            BasicBlock *errorBB = BasicBlock::Create(Ctx, "errorBB", &F);

            // Insert the conditional branch in the checkBB
            checkBuilder.CreateCondBr(isCorrectTarget, thenBB, errorBB);

            // Build the thenBB block (executed if IDs match)
            IRBuilder<> thenBuilder(thenBB);
            thenBuilder.CreateStore(ConstantInt::get(Type::getInt1Ty(Ctx), true), branchCheckingON);
            thenBuilder.CreateBr(origBB);  // Continue to the original instructions

            // Build the errorBB block (executed if IDs do not match)
            IRBuilder<> errorBuilder(errorBB);
            Value* funcName = errorBuilder.CreateGlobalStringPtr(F.getName());
            Value* blockIdValue = ConstantInt::get(Type::getInt32Ty(Ctx), blockID);
            Value *functionStr = errorBuilder.CreateGlobalStringPtr("Error in function: %s , #Basic block: %d , Mismatched branch target! \n \0");
            errorBuilder.CreateCall(fprintFunc, {functionStr, funcName, blockIdValue});
            errorBuilder.CreateCall(printCPUFunc);
            llvm::Value* libraryNameArg = errorBuilder.CreateGlobalStringPtr(LIBRARYNAME);
            errorBuilder.CreateCall(fprintFunc, errorBuilder.CreateGlobalStringPtr("Error occurred on: "));
            errorBuilder.CreateCall(printDateFunc, libraryNameArg);
            errorBuilder.CreateRet(ConstantInt::get(Type::getInt32Ty(Ctx), -1));

            // Build the skipCheckBB block (executed if branch checking is not enabled)
            IRBuilder<> skipBuilder(skipCheckBB);
            skipBuilder.CreateBr(origBB);  // Continue with the original instructions
        }

        bool runOnFunction(Function &F) override {
            if (isExcludedFunction(&F)) {
                errs() << "Skipping function: " << F.getName() << "\n";
                return false;
            }

            LLVMContext &Ctx = F.getContext();

            // Declare external functions used for printing and error handling
            FunctionCallee fprintFunc = F.getParent()->getOrInsertFunction(
                "fprintFunc", FunctionType::get(IntegerType::getInt32Ty(Ctx),
                PointerType::get(Type::getInt8Ty(Ctx), 0)));

            FunctionCallee printCPUFunc = F.getParent()->getOrInsertFunction(
                "print_cpu_id", FunctionType::get(Type::getVoidTy(Ctx), false));

            FunctionCallee printDateFunc = F.getParent()->getOrInsertFunction(
                "print_date", FunctionType::get(Type::getVoidTy(Ctx), Type::getInt8PtrTy(Ctx), false));

            // Get or create the global variables for branch target address and branch checking ON
            GlobalVariable* branchTargetAddress = F.getParent()->getNamedGlobal("llvmPassBranchTargetAddress");
            if (!branchTargetAddress) {
                branchTargetAddress = new GlobalVariable(
                    *F.getParent(), Type::getInt32Ty(Ctx), false,
                    GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(Ctx), 0),
                    "llvmPassBranchTargetAddress");
                branchTargetAddress->setThreadLocal(true); // Make it thread-local
            }

            GlobalVariable* branchCheckingON = F.getParent()->getNamedGlobal("llvmPassBranchCheckingON");
            if (!branchCheckingON) {
                branchCheckingON = new GlobalVariable(
                    *F.getParent(), Type::getInt1Ty(Ctx), false,
                    GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt1Ty(Ctx), false),
                    "llvmPassBranchCheckingON");
                branchCheckingON->setThreadLocal(true); // Make it thread-local
            }

            // Initialize data structures for processing
            std::vector<BasicBlock*> bbs;
            std::map<BasicBlock*, unsigned> blockIDMap;
            std::set<BasicBlock*> blocksWithCheck;
            std::map<BasicBlock*, std::vector<Instruction*>> blockInstructionMap;

            // Assign unique IDs to basic blocks and collect them
            for (BasicBlock &BB : F) {
                blockIDMap[&BB] = globalBlockCounter++; // Assign a global unique block ID
            }

            // If this is the first time, collect basic blocks and their instructions
            if (!countedBlocks) {
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

                // Count total basic blocks in the module
                countBasicBlocks(F.getParent());
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
                        // Found a conditional branch instruction
                        BasicBlock *trueTarget = condBranchInst->getSuccessor(0);
                        BasicBlock *falseTarget = condBranchInst->getSuccessor(1);
                        errs() << "Conditional branch found in basic block " << blockIDMap[BB]
                               << " with true target: " << blockIDMap[trueTarget]
                               << " and false target: " << blockIDMap[falseTarget] << "\n";

                        // Insert code to save the expected block ID based on the condition value
                        IRBuilder<> builder(condBranchInst);

                        // Create constants for the target block IDs
                        Value *trueTargetID = ConstantInt::get(Type::getInt32Ty(Ctx), blockIDMap[trueTarget]);
                        Value *falseTargetID = ConstantInt::get(Type::getInt32Ty(Ctx), blockIDMap[falseTarget]);

                        // Depending on the branch condition, store the appropriate target ID
                        Value *cond = condBranchInst->getCondition();
                        Value *expectedID = builder.CreateSelect(cond, trueTargetID, falseTargetID);

                        // Store the selected ID in the global variable branchTargetAddress
                        builder.CreateStore(expectedID, branchTargetAddress, true);
                        builder.CreateStore(ConstantInt::get(Type::getInt1Ty(Ctx), true), branchCheckingON);

                        // Insert ID checks in the target basic blocks
                        insertIDCheck(Ctx, trueTarget, blockIDMap[trueTarget],
                                      branchTargetAddress, branchCheckingON,
                                      fprintFunc, printCPUFunc, printDateFunc, F, blocksWithCheck);

                        insertIDCheck(Ctx, falseTarget, blockIDMap[falseTarget],
                                      branchTargetAddress, branchCheckingON,
                                      fprintFunc, printCPUFunc, printDateFunc, F, blocksWithCheck);
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
            errs() << "Total basic blocks in module: " << totalBasicBlocks << "\n";
        }

    };
}

// Initialize static variables
unsigned BranchPass::blockCounter = 1;
unsigned BranchPass::globalBlockCounter = 1;
unsigned BranchPass::totalBasicBlocks = 0;
bool BranchPass::countedBlocks = false;

// Register the pass
char BranchPass::ID = 0;

static RegisterPass<BranchPass> X("branchpass", "Insert checks for conditional branch instructions", false, false);

static void registerBranchPass(const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new BranchPass());
}

static RegisterStandardPasses RegisterBranchPass(PassManagerBuilder::EP_OptimizerLast, registerBranchPass);
