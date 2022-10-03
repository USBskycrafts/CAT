#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SparseBitVector.h"
#include <set>
#include <unordered_set>
#include <vector>
#include <map>
#include <unordered_map>
using namespace llvm;
using namespace std;

namespace {
  struct CAT : public FunctionPass {
    static char ID;
    unordered_map<Instruction*, int> inst_label;
    unordered_map<int, Instruction*> label_inst; 
    unordered_map<Instruction*, BitVector> inst_bitvector;
    unsigned inst_count = 0;
    unordered_map<int, BitVector> label_set;
    set<StringRef> CAT_Function;
    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      CAT_Function.insert("CAT_new");
      CAT_Function.insert("CAT_add");
      CAT_Function.insert("CAT_sub");
      CAT_Function.insert("CAT_set");
      return false;
    }
   
    void addLabel(CallInst *inst) {
      label_inst[inst_count] = inst;
      inst_label[inst] = inst_count++;
    }
    
    void setBitVector() {
      for(auto &[inst, label] : inst_label) {
        BitVector vec(inst_count, false);
        vec[label] = true;
        inst_bitvector[inst] = vec;
      }
    }

    void setCluster(CallInst *inst) {
      auto fun_name = inst->getCalledFunction()->getName();
      if(fun_name == "CAT_new") {
        label_set[inst_label[inst]] |= inst_bitvector[inst];
      } else if(CAT_Function.count(fun_name)){
        auto origin_inst = cast<CallInst>(inst->getArgOperand(0));
        label_set[inst_label[origin_inst]] |= inst_bitvector[inst];
      }
    }

    void printGenAndKill(Instruction *inst) {
      errs() << "INSTRUCTION: " << *inst << "\n***************** GEN\n{\n";
      StringRef fun_name;
      if(isa<CallInst>(inst)) fun_name = cast<CallInst>(inst)->getCalledFunction()->getName();
      BitVector bit_vec; 
      if(fun_name == "CAT_new") {
        bit_vec = label_set[inst_label[inst]];
        errs() << " " << *inst << "\n";
      } else if(CAT_Function.count(fun_name)) {
        CallInst *cal_inst = cast<CallInst>(inst->getOperand(0));
        bit_vec = label_set[inst_label[cal_inst]];
        errs() << " " << *inst << "\n";
      }
      errs() << "}\n**************************************\n";
      errs() << "***************** KILL\n{\n";
      if(fun_name == "CAT_new") {
        bit_vec ^= inst_bitvector[inst];
        for(unsigned int i = 0; i < bit_vec.size(); i++) {
          if(bit_vec[i] == true)errs() << " " << *label_inst[i] << "\n";
        }
      } else if(CAT_Function.count(fun_name)) {
        bit_vec ^= inst_bitvector[inst];
        for(unsigned int i = 0; i < bit_vec.size(); i++) {
          if(bit_vec[i] == true)errs() << " " << *label_inst[i] << "\n";
        }
      }
      errs() << "}\n**************************************\n\n\n\n";
    }
    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      errs() << "Function \"" << F.getName() << "\" \n";
      for(auto &inst : instructions(F)) {
        if(isa<CallInst>(inst)) {
          CallInst &cal_inst = cast<CallInst>(inst);
          addLabel(&cal_inst);
        }
      }
      setBitVector();
      for(auto &inst : instructions(F)) {
        if(isa<CallInst>(inst)) {
          CallInst &cal_inst = cast<CallInst>(inst);
          setCluster(&cal_inst);
        }
      }

      for(auto &inst : instructions(F)) {
          printGenAndKill(&inst);
      }
      return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
    }
  };
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());}}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); }}); // ** for -O0
