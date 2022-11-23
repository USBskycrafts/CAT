#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include <climits>
#include <concepts>
#include <set>
#include <unordered_set>
#include <vector>
#include <map>
#include <unordered_map>
#include <thread>


#define DEBUG

using namespace llvm;

namespace {

  enum CAT_Type {
    NONE = 0,
    CAT_NEW,
    CAT_SET,
    CAT_ADD,
    CAT_SUB,
    CAT_GET,
    PHI,
    STORE,
    LOAD,
    OTHER_ESC
  };

  struct CAT : public FunctionPass {
    static char ID; 
    std::unordered_map<Value*, CAT_Type> catType;
    std::unordered_map<Value*, std::set<CallInst*>> defSets;
    std::unordered_map<Instruction*, std::set<CallInst*>> gens, kills;
    std::unordered_map<Instruction*, std::set<CallInst*>> ins, outs;
    std::queue<Instruction*> delList;
    std::unordered_map<Instruction*, std::set<CallInst*>> mayAlias, mustAlias;
    CAT() : FunctionPass(ID) {}
    

    void setCATType(Instruction *inst) {
      if(isa<PHINode>(inst)) {
        catType[inst] = PHI;
      } else if(isa<LoadInst>(inst)) {
        catType[inst] = LOAD;
      } else if(isa<StoreInst>(inst)) {
        catType[inst] = STORE;
      } else if(isa<CallInst>(inst)) {
        auto callInst = cast<CallInst>(inst);
        auto funName = callInst->getCalledFunction()->getName();
        if(funName == "CAT_new") {
          catType[callInst] = CAT_NEW;
        } else if(funName == "CAT_add") {
          catType[callInst] = CAT_ADD;
        } else if(funName == "CAT_sub") {
          catType[callInst] = CAT_SUB;
        } else if(funName == "CAT_set") {
          catType[callInst] = CAT_SET;
        } else if(funName == "CAT_get") {
          catType[callInst] = CAT_GET;
        } else {
          for(auto &operand : callInst->operands()) {
            if(catType[operand] == CAT_NEW) {
              catType[callInst] = OTHER_ESC;
              return;
            }
          }
          catType[callInst] = NONE;
        }
      }
    }

    void setCATTypes(Function &F) {
      for(auto &inst : instructions(F)) {
        setCATType(&inst);
      }
    }

    void setDefSet(CallInst* callInst) {
      auto operand0 = callInst->getOperand(0);
      switch(catType[callInst]) {
        case CAT_NEW:
          defSets[callInst].insert(callInst);
          break; 
        case CAT_ADD:
        case CAT_SET:
        case CAT_SUB:
          defSets[operand0].insert(callInst);
          break;
        default:
          break;
      }
    }

    void setDefSets(Function &F) {
      for(auto &inst : instructions(F)) {
        if(auto callInst = dyn_cast<CallInst>(&inst)) {
          setDefSet(callInst);
        }
      }
    }

    void printGenAndKill(Instruction* inst) {
      #ifdef DEBUG
      errs() << "INSTRUCTION: " << *inst << "\n";
      errs() << "***************** GEN\n{\n";
      for(auto inst_iter : gens[inst]) {
        errs() << " " << *inst_iter << "\n";
      }
      errs() << "}\n**************************************\n";
      errs() << "***************** KILL\n{\n";
      for(auto inst_iter : kills[inst]) {
        errs() << " " << *inst_iter << "\n";
      }
      errs() << "}\n**************************************\n\n\n\n";
      #endif
    }

    void printGensAndKills(Function &F) {
      #ifdef DEBUG
      errs() << "Function \"" << F.getName() << "\" \n";
      for(auto &inst : instructions(F)) {
        printGenAndKill(&inst);
      }
      #endif
    }

    void setAlias(Function &F) {
      AliasAnalysis &aa = getAnalysis<AAResultsWrapperPass>().getAAResults();
      std::vector<LoadInst*> loadList;
      std::vector<StoreInst*> storeList;
      for(auto &inst : instructions(F)) {
        if(isa<LoadInst>(inst)) loadList.push_back(cast<LoadInst>(&inst));
        else if(isa<StoreInst>(inst)) storeList.push_back(cast<StoreInst>(&inst));
      }

      for(auto loadInst : loadList) {
        for(auto storeInst : storeList) {
          auto loadAddress = MemoryLocation::get(loadInst);
          auto storeAddress = MemoryLocation::get(storeInst);
          switch(aa.alias(loadAddress, storeAddress)) {
            case AliasResult::MustAlias:
            {
              auto escInst = storeInst->getValueOperand();
              if(catType[escInst] == CAT_NEW) {
                mustAlias[loadInst].insert(cast<CallInst>(escInst));
              }
              break;
            }
            case AliasResult::MayAlias:
            {
              auto escInst = storeInst->getValueOperand();
              if(catType[escInst] == CAT_NEW) {
                mayAlias[loadInst].insert(cast<CallInst>(escInst));
              }
              break;
            }
            default:
              break;
          }
        }
      }
    }


    bool getModRef(CallInst *callInst, unsigned index) {
      auto arg = callInst->getCalledFunction()->getArg(index);
      errs() << *arg << "\n";
      for(auto &inst : instructions(*callInst->getCalledFunction())) {
        if(auto *callInst_inner = dyn_cast<CallInst>(&inst)) {
          switch(catType[callInst_inner]) {
            case CAT_SET:
            case CAT_ADD:
            case CAT_SUB:
            {
              auto operand0 = callInst_inner->getOperand(0);
              if(arg == operand0) return true;
              break;
            }
            case OTHER_ESC:
            {
              bool willMod = false;
              for(unsigned i = 0; i < callInst_inner->getNumOperands(); i++) {
                if(callInst_inner->getOperand(i) == arg) {
                  willMod |= getModRef(callInst_inner, i);
                }
              }
              return willMod;
              break;
            }
            default:
              break;
          }
        }
      }
      return false;
    }

    std::mutex genLock;
    void setGenAndKill(Instruction* inst) {
      auto operand0 = inst->getOperand(0);
      std::set<CallInst*> defSet;
      switch (catType[inst]) {
        case CAT_NEW:
          defSet = defSets[inst];
          break;
        case CAT_ADD:
        case CAT_SUB:
        case CAT_SET:
        {
          defSet = defSets[operand0];
          if(catType[operand0] == LOAD) {
            auto loadInst = cast<LoadInst>(operand0);
            for(auto cat_new : mustAlias[loadInst]) {
              auto aliasDefSets = defSets[cat_new];
              set_union(defSet.begin(), defSet.end(), aliasDefSets.begin(), aliasDefSets.end(), inserter(defSet, defSet.begin()));
            }
          }
          break;
        }
        case OTHER_ESC:
        {
          unsigned index_num = cast<CallInst>(inst)->getNumOperands();
          errs() << index_num << "\n";
          for(unsigned i = 0; i < index_num - 1; i++) {
            auto willMode = getModRef(cast<CallInst>(inst), i);
            if(willMode == 1) {
              if(catType[inst->getOperand(i)] == CAT_NEW) {
                auto catDefSet = defSets[inst->getOperand(i)];
                set_union(defSet.begin(), defSet.end(), catDefSet.begin(), catDefSet.end(), inserter(defSet, defSet.begin()));
              }
            }
          }
          break;
        }
        default:
          break;
      }
      auto type = catType[inst];
      std::unique_lock<std::mutex> lock(genLock);
      auto &gen = gens[inst], &kill = kills[inst];
      lock.unlock();
      switch(type) {
        case CAT_ADD:
        case CAT_SUB:
        case CAT_SET:
        case CAT_NEW:
          gen.insert(cast<CallInst>(inst));
          set_difference(defSet.begin(), defSet.end(), gen.begin(), gen.end(), inserter(kill, kill.begin()));
          break;
        case OTHER_ESC:
        {
          kill = defSet;
          break;
        }
        default:
          break;
      }
    }

    void setGensAndKills(Function &F) {
      for(auto &inst : instructions(F)) {
        if(auto callInst = dyn_cast<CallInst>(&inst)) {
          std::thread task(&CAT::setGenAndKill, this, callInst);
          task.join();
        }
      }
    }


    void setInsAndOuts(Function &F) {
      std::queue<BasicBlock*> workList;
      for(auto &BB : F) {
        workList.push(&BB);
      }

      while(!workList.empty()) {
        auto &BB = workList.front();
        workList.pop();
        auto &headInst = BB->front();
        auto tailInst = BB->getTerminator();
        auto out_old = outs[tailInst], gen = gens[&headInst], kill = kills[&headInst];
        std::set<CallInst*> in = {}, out = {};
        for(auto prev_BB : predecessors(BB)) {
          auto prev_out = outs[prev_BB->getTerminator()];
          set_union(prev_out.begin(), prev_out.end(), in.begin(), in.end(), inserter(in, in.begin()));
        }
        set_difference(in.begin(), in.end(), kill.begin(), kill.end(), inserter(out, out.begin()));
        set_union(out.begin(), out.end(), gen.begin(), gen.end(), inserter(out, out.begin()));
        ins[&headInst] = in;
        outs[&headInst] = out;
        

        auto *cur = headInst.getNextNode();
        while(cur != nullptr) {
          in = out;
          out = {};
          ins[cur] = in;
          gen = gens[cur], kill = kills[cur];
          set_difference(in.begin(), in.end(), kill.begin(), kill.end(), inserter(out, out.begin()));
          set_union(out.begin(), out.end(), gen.begin(), gen.end(), inserter(out, out.begin()));
          outs[cur] = out;
          cur = cur->getNextNode();
        }

        if(out != out_old) {
          for(auto nextBB : successors(BB)) workList.push(nextBB);
        }
      }
    }

    void printInAndOut(Instruction* inst) {
      #ifdef DEBUG
      errs() << "INSTRUCTION: " << *inst << "\n";
      errs() << "***************** IN\n{\n";
      for(auto inst_iter : ins[inst]) {
        errs() << " " << *inst_iter << "\n";
      }
      errs() << "}\n**************************************\n";
      errs() << "***************** OUT\n{\n";
      for(auto inst_iter : outs[inst]) {
        errs() << " " << *inst_iter << "\n";
      }
      errs() << "}\n**************************************\n\n\n\n";
      #endif
    }

    void printInsAndOuts(Function &F) {
      #ifdef DEBUG
      errs() << "Function \"" << F.getName() << "\" \n";
      for(auto &inst : instructions(F)) {
        printInAndOut(&inst);
      }
      #endif
    }

    std::unordered_set<int64_t> phiNodeFolding(PHINode *phi) {
      std::unordered_set<int64_t> constants;
      std::queue<PHINode*> phiList;
      phiList.push(phi);
      while(!phiList.empty()) {
        auto phiNode = phiList.front();
        phiList.pop();

        for(auto &operand : phiNode->operands()) {
          if(isa<PHINode>(operand)) phiList.push(cast<PHINode>(operand));
          else if(isa<ConstantInt>(operand)) {
            constants.insert(cast<ConstantInt>(operand)->getSExtValue());
          } else if(isa<Instruction>(operand)) {
            auto inst = cast<Instruction>(operand);
            switch(catType[inst]) {
              case CAT_NEW:
                if(isa<ConstantInt>(inst->getOperand(0))) {
                  constants.insert(cast<ConstantInt>(inst->getOperand(0))->getSExtValue());
                } else {
                  return {};
                }
                break;
              case CAT_SET:
                if(isa<ConstantInt>(inst->getOperand(1))) {
                  constants.insert(cast<ConstantInt>(inst->getOperand(1))->getSExtValue());
                } else {
                  return {};
                }
                break;
              case LOAD:
              {
                auto loadInst = cast<LoadInst>(operand);
                for(auto callInst : mustAlias[loadInst]) {
                  switch (catType[callInst]) {
                    case CAT_NEW:
                      if(isa<ConstantInt>(callInst->getOperand(0))) {
                        constants.insert(cast<ConstantInt>(callInst->getOperand(0))->getSExtValue());
                      } else {
                        return {};
                      }
                      break;
                    case CAT_SET:
                      if(isa<ConstantInt>(callInst->getOperand(1))) {
                        constants.insert(cast<ConstantInt>(callInst->getOperand(1))->getSExtValue());
                      } else {
                        return {};
                      }
                      break;
                    default:
                      break;
                    }
                }
                for(auto callInst : mayAlias[loadInst]) {
                  switch (catType[callInst]) {
                    case CAT_NEW:
                      if(isa<ConstantInt>(callInst->getOperand(0))) {
                        constants.insert(cast<ConstantInt>(callInst->getOperand(0))->getSExtValue());
                      } else {
                        return {};
                      }
                      break;
                    case CAT_SET:
                      if(isa<ConstantInt>(callInst->getOperand(1))) {
                        constants.insert(cast<ConstantInt>(callInst->getOperand(1))->getSExtValue());
                      } else {
                        return {};
                      }
                      break;
                    default:
                      break;
                    }
                }
                break;
              }
              default:
                break;
            }
          }
        }
      }
      return constants;
    }

    void CAT_SETPropagation(CallInst *callInst) {
      auto operand0 = callInst->getOperand(0);
      auto next = callInst->getNextNode();
      if(next->getNumOperands() >= 1 && next->getOperand(0) == operand0) {
        switch(catType[next]) {
          case CAT_ADD:
          case CAT_SUB:
          {
            if(operand0 == next->getOperand(0) && next->getOperand(1) != operand0 && next->getOperand(2) != operand0) {
              delList.push(callInst);
            }
            break;
          }
          case CAT_SET:
            if(operand0 == next->getOperand(0)) {
              delList.push(callInst);
            }
            break;
          default:
            break;
        }
      }
    }

    void CATFolding(CallInst* callInst) {
      auto operand1 = callInst->getOperand(1), operand2 = callInst->getOperand(2);
      auto in = ins[callInst];
      std::set<int64_t> constants1, constants2;
      std::set<Instruction*> inst1_set, inst2_set;
      for(auto inst : in) {
        switch(catType[inst]) {
          case CAT_NEW:
          {
            if(inst == operand1) {
              inst1_set.insert(inst);
            }
            if(inst == operand2) {
              inst2_set.insert(inst);
            }
            break;
          }
          case CAT_SET:
          case PHI:
          {
            if(inst->getOperand(0) == operand1) {
              inst1_set.insert(inst);
            }
            if(inst->getOperand(0) == operand2) {
              inst2_set.insert(inst);
            }
            break;
          }
          case CAT_ADD:
          case CAT_SUB:
          {
            if(inst->getOperand(0) == operand1 || inst->getOperand(0) == operand2) return;
            break;
          }
          default:
            break;
        }
      }

      for(auto inst1 : inst1_set) {
        switch(catType[inst1]) {
          case CAT_NEW:
          {
            if(isa<ConstantInt>(inst1->getOperand(0))) {
              constants1.insert(cast<ConstantInt>(inst1->getOperand(0))->getSExtValue());
            }
            break;
          } 
          case CAT_SET:
          {
            if(isa<ConstantInt>(inst1->getOperand(1))) {
              constants1.insert(cast<ConstantInt>(inst1->getOperand(1))->getSExtValue());
            }
            break;
          } 
          case PHI:
          {
            auto phi_constants = phiNodeFolding(cast<PHINode>(inst1));
            set_union(constants1.begin(), constants1.end(), phi_constants.begin(), phi_constants.end(), inserter(constants1, constants1.begin()));
            break;
          }
          default:
            break;
        }
      }
  
      for(auto inst2 : inst2_set) {
        switch(catType[inst2]) {
          case CAT_NEW:
          {
            if(isa<ConstantInt>(inst2->getOperand(0))) {
              constants2.insert(cast<ConstantInt>(inst2->getOperand(0))->getSExtValue());
            }
            break;
          } 
          case CAT_SET:
          {
            if(isa<ConstantInt>(inst2->getOperand(1))) {
              constants2.insert(cast<ConstantInt>(inst2->getOperand(1))->getSExtValue());
            }
            break;
          } 
          case PHI:
          {
            auto phi_constants = phiNodeFolding(cast<PHINode>(inst2));
            set_union(constants2.begin(), constants2.end(), phi_constants.begin(), phi_constants.end(), inserter(constants2, constants2.begin()));
            break;
          }
          default:
            break;
        }
      }


      std::set<int64_t> constants;
      if(catType[callInst] == CAT_ADD) {
        for(auto num1 : constants1)  {
          for(auto num2 : constants2) {
            constants.insert(num1 + num2);
          }
        }
      } else if(catType[callInst] == CAT_SUB) {
        for(auto num1 : constants1) {
          for(auto num2 : constants2) {
            constants.insert(num1 - num2);
          }
        }
      }

      if(constants.size() == 1) {
        IRBuilder<> builder(callInst->getNextNode());
        auto call = builder.CreateCall(callInst->getModule()->getFunction("CAT_set"), {
          callInst->getOperand(0),
          ConstantInt::get(IntegerType::get(callInst->getModule()->getContext(), 64), *constants.begin()),
        });
        catType[call] = CAT_SET;
        delList.push(callInst);
      }
    }

    void CAT_GETPropagation(CallInst *callInst) {
      auto in = ins[callInst];
      std::set<int64_t> constants;
      auto operand0 = callInst->getOperand(0);
      for(auto &inst : in) {
        switch(catType[inst]) {
          case CAT_NEW:
          {
            if(inst == operand0 && isa<ConstantInt>(inst->getOperand(0))) {
              constants.insert(cast<ConstantInt>(inst->getOperand(0))->getSExtValue());
            }
            break;
          }
          case CAT_SET:
          {
            if(inst->getOperand(0) == operand0 && isa<ConstantInt>(inst->getOperand(1))) {
              constants.insert(cast<ConstantInt>(inst->getOperand(1))->getSExtValue());
            }
            break;
          }
          case CAT_ADD:
          case CAT_SUB:
            if(inst->getOperand(0) == operand0) return;
            break;
          default:
            break;
        }
      }
      if(constants.size() == 1) {
        callInst->replaceAllUsesWith(
          ConstantInt::get(IntegerType::get(callInst->getModule()->getContext(), 64), *constants.begin()));
        delList.push(callInst);
      }
    }


    void doConstantPropagation(Function &F) {
      std::queue<Instruction*> instList;
      for(auto &inst : instructions(F)) {
        instList.push(&inst);
      }
      while(!instList.empty()) {
        auto inst = instList.front();
        instList.pop();
        switch(catType[inst]) {
          case CAT_SET:
            CAT_SETPropagation(cast<CallInst>(inst));
            break;
          case CAT_ADD:
          case CAT_SUB:
            CATFolding(cast<CallInst>(inst));
            break;
          case CAT_GET:
            CAT_GETPropagation(cast<CallInst>(inst));
            break;
          default:
            break;
        }
      }
      while(!delList.empty()) {
        auto inst = delList.front();
        delList.pop();
        inst->eraseFromParent();
      }
    }

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      // for(auto &F : M) {
        setCATTypes(F);
        setDefSets(F);
        setAlias(F);
      // }
      // for(auto &F : M)  {
        setGensAndKills(F);
        setInsAndOuts(F);
        //printInsAndOuts(F);
        doConstantPropagation(F);
      // }
      return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<AAResultsWrapperPass>();
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