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
    unordered_map<Instruction*, BitVector> gen, kill, in, out;
    queue<Instruction*> q;
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
        auto first_Op = inst->getOperand(0);
        if(isa<PHINode>(first_Op)) {
          auto phi = cast<PHINode>(first_Op);
          for(unsigned i = 0; i < phi->getNumOperands(); i++) {
            if(isa<CallInst>(phi->getOperand(i))) {
              label_set[inst_label[cast<CallInst>(phi->getOperand(i))]] |= inst_bitvector[inst];
            }
          }
        } else {
            auto origin_inst = cast<Instruction>(inst->getArgOperand(0));
            label_set[inst_label[origin_inst]] |= inst_bitvector[inst];
        }
      }
    }

    void setGenAndKill(Instruction *inst) {
      StringRef fun_name;
      if(isa<CallInst>(inst)) fun_name = cast<CallInst>(inst)->getCalledFunction()->getName();
      BitVector bit_vec(inst_count, false); 
      if(fun_name == "CAT_new") {
        bit_vec = label_set[inst_label[inst]];
        gen[inst] = inst_bitvector[inst];
      } else if(CAT_Function.count(fun_name)) {
        auto cat_new = inst->getOperand(0);
        if(auto phi = dyn_cast<PHINode>(cat_new)) {
          //errs() << *inst << " " << *phi << "\n";
          bit_vec |= inst_bitvector[inst];
          for(unsigned i = 0; i < phi->getNumOperands(); i++) {
            auto cat_new = phi->getOperand(i);
            //errs() << *cat_new << "\n";
            if(auto call_new = dyn_cast<CallInst>(cat_new)) {
              //bit_vec |= label_set[inst_label[call_new]];
            } 
          }
        } else {
          CallInst *cal_inst = cast<CallInst>(inst->getOperand(0));
          bit_vec = label_set[inst_label[cal_inst]];
        }
        gen[inst] = inst_bitvector[inst];
      } else {
        gen[inst] = BitVector(inst_count, false);
      }

      if(CAT_Function.count(fun_name)) {
        bit_vec ^= inst_bitvector[inst];
        kill[inst] = bit_vec;
      } else {
        kill[inst] = BitVector(inst_count, false);
      }
    }

    
    void setInAndOut(Function &F) {
      for(auto &inst : instructions(F)) {
        q.push(&inst);
      } 
      while(!q.empty()) {
        auto &inst = q.front();
        auto bb = inst->getParent();
        q.pop();
        BitVector in_bit(inst_count, false), out_bit(inst_count, false);
        BitVector gen_bit = gen[inst], kill_bit = kill[inst];
        auto oldOut = out[inst];
        if(&bb->front() == inst) {
          for(auto prev : predecessors(bb)) {
            auto inst_prev = prev->getTerminator();
            in_bit |= out[inst_prev];
          }
        } else {
          in_bit = out[inst->getPrevNode()];
        }
        
        out_bit = in_bit;
        out_bit |= gen_bit;
        out_bit &= kill_bit.flip();
        in[inst] = in_bit;
        out[inst] = out_bit;
        /**
        errs() << *inst << "\n" ;
        for(int i = 0; i < gen[inst].size(); i++) {
          errs() << gen[inst][i];
        }
        errs() << "\n";
        for(int i = 0; i < kill[inst].size(); i++) {
          errs() << kill[inst][i];
        }
        errs() << "\n";
        for(int i = 0; i < in[inst].size(); i++) {
          errs() << in[inst][i];
        }
        errs() << "\n";
        for(int i = 0; i < out[inst].size(); i++) {
          errs() << out[inst][i];
        }
        errs() << "\n";
        **/
        if(out_bit != oldOut) {
          if(inst == bb->getTerminator()) {
              for(auto next : successors(bb)) {
                q.push(&next->front());
              }
          } else {
            q.push(inst->getNextNode());
          }
        }
      }
    }

    void printInAndOut(Function &F) {
      for(auto &inst : instructions(F)) {
        /**
        auto gen_bit = gen[&inst];
        for(unsigned i = 0; i < gen_bit.size(); i++) errs() << gen_bit[i];
        errs() << "\n";
        auto kill_bit = kill[&inst];
        for(unsigned i = 0; i < kill_bit.size(); i++) errs() << kill_bit[i];;
        errs() << "\n";
        **/
        auto in_bit = in[&inst]; 
        errs() << "INSTRUCTION: " << inst << "\n";
        errs() << "***************** IN\n{\n";
        for(unsigned i = 0; i < in_bit.size(); i++) {
          if(in_bit[i] == true) errs() << " " << *label_inst[i] << "\n";
        }
        errs() << "}\n**************************************\n";
        errs() << "***************** OUT\n{\n";
        auto out_bit = out[&inst];
        for(unsigned i = 0; i < out_bit.size(); i++) {
          if(out_bit[i] == true) errs() << " " << *label_inst[i] << "\n";
        }
        errs() << "}\n**************************************\n\n\n\n";
      }
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
          auto &cal_inst = cast<CallInst>(inst);
          setCluster(&cal_inst);
        }
      }
      for(auto &inst : instructions(F)) {
          setGenAndKill(&inst);
      }
      setInAndOut(F);
      printInAndOut(F);
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
