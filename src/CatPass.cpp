#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include <algorithm>
#include <climits>
#include <concepts>
#include <iostream>
#include <list>
#include <map>
#include <queue>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace llvm;
using namespace std;
namespace {
struct CAT : public ModulePass {
  static char ID;
  unordered_map<Value *, int> valueLabel; // ssaVar contains cat_new cat_add
                                           // cat_sub cat_set and new function
  unordered_map<int, Value *> labelValue;
  unordered_map<Value *, BitVector> GEN, KILL, IN, OUT;
  set<StringRef> catFunctionName;
  unordered_map<Value *, BitVector> mayAlias;
  unordered_map<int, BitVector> mustAlias;
  unordered_map<Value *, BitVector> instBits;
  int totalCnt = 0;
  bool isPause = true;
  vector<bool> ssaVarDel;
  CAT() : ModulePass(ID) {}

  bool doInitialization(Module &M) override {
    catFunctionName.insert("CAT_new");
    catFunctionName.insert("CAT_add");
    catFunctionName.insert("CAT_sub");
    catFunctionName.insert("CAT_set");
    return false;
  }
  void clear() {
    valueLabel.clear();
    labelValue.clear();
    GEN.clear();
    KILL.clear();
    IN.clear();
    OUT.clear();
    mustAlias.clear();
    instBits.clear();
    totalCnt = 0;
  }
  void setCluster(Instruction *ins) {
    if (auto inst = dyn_cast<CallInst>(ins)) {
      auto funcName = inst->getCalledFunction()->getName();
      if (funcName == "CAT_new") {
        mustAlias[valueLabel[ins]] |= instBits[ins];
      } else if (catFunctionName.count(funcName)) {
        auto op = dyn_cast<Instruction>(inst->getOperand(0));
        if (funcName == "CAT_set" && isa<SExtInst>(inst->getOperand(1)))
          return;
        if (isa<PHINode>(inst->getOperand(
                0))) // we need a queue to get everything of this instruction
        {
          auto phi = dyn_cast<PHINode>(inst->getOperand(0));
          queue<PHINode *> q;
          q.push(phi);
          while (!q.empty()) {
            auto tmp = q.front();
            q.pop();
            for (uint i = 0; i < tmp->getNumOperands(); ++i) {
              if (auto calVar = dyn_cast<CallInst>(tmp->getOperand(i))) {
                if (calVar->getCalledFunction()->getName() == "CAT_new") {
                  if (valueLabel.find(calVar) != valueLabel.end())
                    mustAlias[valueLabel[calVar]] |= instBits[inst];
                }
              } else if (auto phiVar = dyn_cast<PHINode>(tmp->getOperand(i))) {
                q.push(phiVar);
              }
            }
          }
        } else {
          if (valueLabel.find(op) != valueLabel.end())
            mustAlias[valueLabel[op]] |= instBits[ins]; // for new
        }
      } else if (valueLabel.count(inst)) {
        for (uint i = 0; i < inst->getNumOperands(); ++i) {
          if (auto var = dyn_cast<CallInst>(inst->getOperand(i))) {
            if (valueLabel.find(var) != valueLabel.end()) {
              mustAlias[valueLabel[var]] |= instBits[ins];
              mayAlias[var] |= instBits[ins];
            }
          }
        }
      }
    } else if (auto inst = dyn_cast<StoreInst>(ins)) {
      auto var = dyn_cast<CallInst>(inst->getValueOperand());
      if (valueLabel.find(var) != valueLabel.end()) {
      }
    }
  }
  void replaceCallInst(CallInst *before, CallInst *after) {
    int index = valueLabel[before];
    valueLabel[after] = index;
    valueLabel.erase(before);
    labelValue[index] = after;
    instBits[after] = instBits[before];
    instBits.erase(before);
    before = nullptr;
  }
  void setGenAndKill(Instruction *ins) {
    BitVector gen(totalCnt, false), kill(totalCnt, false);
    if (isa<CallInst>(ins)) {
      auto inst = dyn_cast<CallInst>(ins);
      auto funcName = inst->getCalledFunction()->getName();
      if (funcName == "CAT_new") {
        gen[valueLabel[ins]] = true;
        kill ^= mustAlias[valueLabel[ins]];
        kill[valueLabel[ins]] = false;
      } else if (catFunctionName.count(funcName) || funcName == "CAT_get") {
        auto var = dyn_cast<Instruction>(inst->getOperand(0));
        if (catFunctionName.count(funcName))
          gen[valueLabel[ins]] = true;
        if (funcName == "CAT_set") {
        }
        if (funcName == "CAT_set" && (isa<SExtInst>(inst->getOperand(1)))) {
          goto fail;
        }
        if (var && isa<PHINode>(var)) {
          queue<PHINode *> q;
          auto p = dyn_cast<PHINode>(var);
          q.push(p);
          while (!q.empty()) {
            auto phi = q.front();
            q.pop();
            for (uint i = 0; i < phi->getNumOperands(); ++i) {
              auto phiVar = phi->getOperand(i);
              if (auto calVar = dyn_cast<CallInst>(phiVar)) {
                if (calVar->getCalledFunction()->getName() == "CAT_new") {
                  kill |= mustAlias[valueLabel[calVar]];
                  kill[valueLabel[calVar]] = false;
                }
              } else if (auto newPhi = dyn_cast<PHINode>(phiVar)) {
                q.push(newPhi);
              }
            }
          }
        } else if (catFunctionName.count(funcName)) {
          if (valueLabel.find(var) != valueLabel.end())
            kill |= mustAlias[valueLabel[var]];
          kill[valueLabel[ins]] = false;
        }
      } else if (valueLabel.find(ins) !=
                 valueLabel.end()) // for new instruction like p
      {
        gen[valueLabel[ins]] = true;
        kill = getModify(dyn_cast<CallInst>(ins));
      }
    } else if (auto inst = dyn_cast<StoreInst>(ins)) {
      kill |=
          mustAlias[valueLabel[dyn_cast<CallInst>(inst->getValueOperand())]];
      kill[valueLabel[inst]] = false;
    } else if (auto inst = dyn_cast<LoadInst>(ins)) {
    }
    fail:;
    GEN[ins] = gen;
    KILL[ins] = kill;
  }
  void setInAndOut(Function &F) {
    queue<Instruction *> q;
    for (auto &I : instructions(F)) {
      setGenAndKill(&I);
      q.push(&I);
    }
    while (!q.empty()) {
      auto tmp = q.front();
      q.pop();
      auto bb = tmp->getParent();
      auto gen = GEN[tmp], kill = KILL[tmp], in = BitVector(totalCnt, false),
           oldOut = OUT[tmp];
      if (tmp == &(bb->front())) // first instruction
      {
        for (auto pa : predecessors(bb)) {
          in |= OUT[pa->getTerminator()];
        }
      } else {
        in |= OUT[tmp->getPrevNode()];
      }
      IN[tmp] = in;
      OUT[tmp] = in;
      OUT[tmp] &= kill.flip();
      OUT[tmp] |= gen;
      if (oldOut != OUT[tmp]) {
        if (bb->getTerminator() == tmp) {
          for (auto son : successors(bb)) {
            q.push(&(son->front()));
          }
        } else {
          q.push(tmp->getNextNode());
        }
      }
    }
  }
  void addValue(Value *I) {
    valueLabel[I] = totalCnt;
    labelValue[totalCnt++] = I;
  }
  void init(Function &F) {
    for (auto &I : instructions(F)) {
      if (isa<CallInst>(&I)) {
        auto inst = dyn_cast<CallInst>(&I);
        auto funcName = inst->getCalledFunction()->getName();
        if (catFunctionName.count(
                funcName)) // may delete in the future about(isa<StoreInst>(&I))
        {
          addValue(&I);
        }
      } else if (isa<StoreInst>(&I))
        addValue(&I);
      else if (isa<LoadInst>(&I)) {
      }
    }
    function<bool(CallInst *)> check = [&](CallInst *inst) {
      bool isVariable = false;
      if (inst->getCalledFunction()->getName() == "CAT_get")
        return isVariable;
      for (uint i = 0; i < inst->getNumOperands(); ++i) {
        if (auto var = dyn_cast<CallInst>(inst->getOperand(i))) {
          isVariable = true;
          break;
        }
      }
      if (isVariable)
        addValue(inst);
      return isVariable;
    };
    for (auto &I : instructions(F)) {
      if (isa<CallInst>(&I)) {
        auto inst = dyn_cast<CallInst>(&I);
        auto funcName = inst->getCalledFunction()->getName();
        if (catFunctionName.count(funcName) || check(inst)) {
          auto tmp = BitVector(totalCnt, false);
          tmp[valueLabel[&I]] = true;
          instBits[&I] = tmp;
        }
      } else if (isa<StoreInst>(&I)) {
        auto tmp = BitVector(totalCnt, false);
        tmp[valueLabel[&I]] = true;
        instBits[&I] = tmp;
      }
    }
    for (auto &I : instructions(F)) {
      if (isa<CallInst>(&I) || isa<StoreInst>(&I) || isa<LoadInst>(&I)) {
        setCluster(&I);
      }
    }
    setInAndOut(F);
  }
  void memoryAlias(CallInst *inst) {
    unordered_set<CallInst *> delList;
    auto op = inst->getOperand(0);
    while (inst->getPrevNode() && isa<CallInst>(inst->getPrevNode()) &&
           catFunctionName.count((dyn_cast<CallInst>(inst->getPrevNode()))
                                 ->getCalledFunction()
                                 ->getName())) {
      auto pre = dyn_cast<CallInst>(inst->getPrevNode());
      if (pre->getOperand(0) == op) {
        ssaVarDel[valueLabel[pre]] = true;
        delList.insert(pre);
      }
      inst = pre;
    }
    for (auto inst : delList)
      inst->eraseFromParent();
  }
  void constantPropagation(Function &F) {
    queue<CallInst *> q;
    ssaVarDel = vector<bool>(totalCnt, false);
    for (auto &I : instructions(F)) {
      if (auto inst = dyn_cast<CallInst>(&I)) {
        auto funcName = inst->getCalledFunction()->getName();
        if ((catFunctionName.count(funcName) && funcName != "CAT_new") ||
            funcName == "CAT_get") {
          q.push(inst);
        }
      }
    }
    unordered_set<CallInst *> delList;
    while (!q.empty()) {
      auto inst = q.front();
      q.pop();
      aliasOptimization(F);
      auto funcName = inst->getCalledFunction()->getName();
      ConstantInt *value = nullptr;
      // bool isDelete=false;
      if ((value = constantFolding(inst))) {
        if (funcName == "CAT_add" || funcName == "CAT_sub") {
          // isDelete=true;
          IRBuilder<> builder(inst);
          CallInst *newInst =
              builder.CreateCall(F.getParent()->getFunction("CAT_set"),
                                 {inst->getOperand(0), value});
          newInst->setTailCall();
          replaceCallInst(inst, newInst);
          inst->eraseFromParent();
          q.push(newInst);
        }
        if (funcName == "CAT_get")
          inst->replaceAllUsesWith(value);
        if ((funcName == "CAT_get" || funcName == "CAT_set") &&
            !deadCodeCheck(inst)) {
          delList.insert(inst);
          if (funcName == "CAT_set")
            ssaVarDel[valueLabel[inst]] = true;
        }
      }
    }
    for (auto &I : delList) {
      I->eraseFromParent();
    }
    for (auto &I : instructions(F)) {
      if (auto calIns = dyn_cast<CallInst>(&I)) {
        if (calIns->getCalledFunction()->getName() == "CAT_set")
          memoryAlias(calIns);
      }
    }
  }
  ConstantInt *uniqueNess(BitVector &instBit) {
    int varCnt = 0;
    ConstantInt *res = nullptr;
    for (uint i = 0; i < instBit.size(); ++i) {
      ConstantInt *value = nullptr;
      if (instBit[i]) {
        ++varCnt;
        auto var = dyn_cast<CallInst>(labelValue[i]);
        if (var == nullptr)
          continue; 
        auto varName = var->getCalledFunction()->getName();
        if (varName == "CAT_new") {
          value = dyn_cast<ConstantInt>(var->getOperand(0));
        } else if (varName == "CAT_set") {
          value = dyn_cast<ConstantInt>(var->getOperand(1));
        } else if (varName == "CAT_add" || varName == "CAT_sub") {
          auto op1 = var->getOperand(1);
          auto op2 = var->getOperand(2);
          if (isa<ConstantInt>(op1) && isa<ConstantInt>(op2)) {
            auto v1 = dyn_cast<ConstantInt>(op1)->getSExtValue();
            auto v2 = dyn_cast<ConstantInt>(op2)->getSExtValue();
            value = ConstantInt::get(
                IntegerType::getInt64Ty(var->getFunction()->getContext()),
                (varName == "CAT_add" ? v1 + v2 : v1 - v2), true);
          }
        }
      }
      if (value) {
        if (res == nullptr || value->getSExtValue() == res->getSExtValue()) {
          --varCnt;
          res = value;
        }
      }
      if (varCnt >= 1)
        return nullptr;
    }
    return res;
  }
  ConstantInt *phiOperand(Value *phi, CallInst *inst) {
    ConstantInt *res = nullptr;
    int varCnt = 0;
    auto phiIns = dyn_cast<PHINode>(phi);
    queue<PHINode *> q;
    q.push(phiIns);
    while (!q.empty()) {
      auto tmp = q.front();
      q.pop();
      for (uint i = 0; i < tmp->getNumOperands(); ++i) {
        ConstantInt *value = nullptr;
        auto var = tmp->getOperand(i);
        if (auto varCal = dyn_cast<CallInst>(var)) {
          if (varCal->getCalledFunction()->getName() == "CAT_new") {
            if (isa<ConstantInt>(varCal->getOperand(0))) {
              ++varCnt;
              auto phiBit = IN[inst];
              phiBit &= mustAlias[valueLabel[varCal]];
              value = uniqueNess(phiBit);
            }
          }
        } else if (isa<PHINode>(var)) {
          q.push(dyn_cast<PHINode>(var));
        }
        if (value) {
          if (res == nullptr || value->getSExtValue() == res->getSExtValue()) {
            --varCnt;
            res = value;
          }
        }
        if (varCnt >= 1)
          return nullptr;
      }
    }
    return res;
  }
  bool deadCodeCheck(CallInst *inst) {
    auto funcName = inst->getCalledFunction()->getName();
    if (funcName == "CAT_set") {
      auto var = inst->getOperand(0);
      return var->getNumUses() > 0;
    } else {
      return inst->getNumUses() > 0;
    }
    return false;
  }
  ConstantInt *constantFolding(CallInst *inst) {
    auto funcName = inst->getCalledFunction()->getName();
    ConstantInt *res = nullptr;
    if (funcName == "CAT_get") {
      auto op = inst->getOperand(0);
      if (auto var = dyn_cast<CallInst>(op)) {
        auto instBit = IN[inst];
        instBit &= mustAlias[valueLabel[var]];
        res = uniqueNess(instBit);
      } else if (auto var = dyn_cast<PHINode>(op)) {
        res = phiOperand(var, inst);
      }
    } else if (funcName == "CAT_add" || funcName == "CAT_sub") {
      auto op1 = inst->getOperand(1);
      auto op2 = inst->getOperand(2);
      if (funcName == "CAT_sub" && op1 == op2) // special situation
      {
        return ConstantInt::get(
            IntegerType::getInt64Ty(inst->getFunction()->getContext()), 0,
            true);
      }
      ConstantInt *v1 = nullptr, *v2 = nullptr;
      if (isa<ConstantInt>(op1))
        v1 = dyn_cast<ConstantInt>(op1);
      else if (isa<PHINode>(op1))
        v1 = phiOperand(op1, inst);
      else if (auto varCal = dyn_cast<CallInst>(op1)) {

        auto opBit = IN[inst];
        mustAlias[valueLabel[varCal]];
        opBit &= mustAlias[valueLabel[varCal]];
        v1 = uniqueNess(opBit);
      }
      if (isa<ConstantInt>(op2))
        v2 = dyn_cast<ConstantInt>(op2);
      else if (isa<PHINode>(op2))
        v2 = phiOperand(op2, inst);
      else if (auto varCal = dyn_cast<CallInst>(op2)) {
        auto opBit = IN[inst];
        opBit &= mustAlias[valueLabel[varCal]];
        v2 = uniqueNess(opBit);
      }
      if (v1 && v2) {
        auto value1 = v1->getSExtValue();
        auto value2 = v2->getSExtValue();
        res = ConstantInt::get(
            IntegerType::getInt64Ty(inst->getFunction()->getContext()),
            funcName == "CAT_add" ? value1 + value2 : value1 - value2, true);
      }
    }
    return res;
  }
  bool aliasOptimization(Function &F) 
  {
    AliasAnalysis &aa = getAnalysis<AAResultsWrapperPass>(F).getAAResults();
    unordered_set<Instruction *> killList;
    for (auto &I : instructions(F)) {
      if (isPause)
        break;
      if (auto inst = dyn_cast<CallInst>(&I)) {
        auto op = inst->getOperand(0);
        for (auto [var, index] : valueLabel) {
          if (auto calVar = dyn_cast<CallInst>(var)) {
            if (calVar->getCalledFunction()->getName() == "CAT_new") {
              switch (aa.alias(op, var)) {
              case AliasResult::MustAlias:
                killList.insert(inst);
                break;
              default:
                break;
              }
            }
          }
        }
      }
    }
    for (auto &I : killList)
      I->eraseFromParent();
    return false;
  }
  BitVector getModify(CallInst *inst) {
    BitVector ans(totalCnt, false);
    AliasAnalysis &aa =
        getAnalysis<AAResultsWrapperPass>(*inst->getFunction()).getAAResults();
    for (uint i = 0; i < inst->getNumOperands(); ++i) {
      uint size = 0;
      if (auto op = dyn_cast<CallInst>(inst->getOperand(i))) {
        if (auto type = dyn_cast<PointerType>(inst->getType())) {
          auto elementPointedType = type->getNonOpaquePointerElementType();
          if (elementPointedType->isSized()) {
            size = inst->getModule()->getDataLayout().getTypeStoreSize(
                elementPointedType);
          }
        }
        if (op->getCalledFunction()->getName() == "CAT_new") {
          switch (aa.getModRefInfo(inst, op, size)) {
          case ModRefInfo::ModRef:
          case ModRefInfo::MustModRef:
          case ModRefInfo::Mod:
            ans |= mustAlias[valueLabel[op]];
            break;
          default:
            break;
          }
        }
      }
    }
    ans[valueLabel[inst]] = false;
    return ans;
  }

  bool isRecursive(CallInst *callInst) {
    // errs() << "CHECK " << *callInst << "if it is recursive\n";
    for(auto &inst : instructions(callInst->getCalledFunction())) {
      if(!isa<CallInst>(inst)) continue;
      auto calledCallInst = cast<CallInst>(&inst);
      if(calledCallInst->getCalledFunction()->getName() == callInst->getCalledFunction()->getName()) {
        // errs() << *callInst << " is a recursive function.\n";
        return true;
      } 
    }
    // errs() << *callInst << " is not a recursive function.\n";
    return false;
  }

  bool isInlinable(CallInst *callInst) {
    // errs() << "CHECK " << *callInst << " if it is inlinable\n";
    auto funName = callInst->getCalledFunction()->getName();
    if(catFunctionName.count(funName) || funName == "CAT_get") return false;
    if(!hasCATOperand(callInst)) return false;
    if(isRecursive(callInst)) return false;
    // errs() << *callInst << " is able to inline\n";
    return true;
  }

  bool hasCATOperand(CallInst* callInst) {
    for(auto &operand : callInst->operands()) {
      if(auto catInst = dyn_cast<CallInst>(operand)) {
        auto funName = catInst->getCalledFunction()->getName();
        if(catFunctionName.count(funName)) {
          // errs() << *callInst << " has CAT instruction\n";
          return true;
        }
      }
    }
    return false;
  }

  void inlinePropagation(Module &M) {
    unordered_set<CallBase *> inlineList;
    for (auto &F : M) {
      for (auto &inst : instructions(F)) {
        if (auto callInst = dyn_cast<CallInst>(&inst)) {
          if (isInlinable(callInst)) {
            inlineList.insert(callInst);
            // errs() << *callInst << " is inlined\n";
          }
        }
      }
    }

    for (auto callInst : inlineList) {
      InlineFunctionInfo ini;
      InlineFunction(*callInst, ini);
    }
  }

  bool runOnModule(Module &M) override {

    inlinePropagation(M);

    for (auto &F : M) {
      init(F);
      constantPropagation(F);
    }
    return false;
  }
  void printUse(Instruction *I) {
    errs() << *I << "::\n";
    if (auto inst = dyn_cast<CallInst>(I)) {
      for (auto usr : inst->users()) {
        if (auto var = dyn_cast<CallInst>(usr)) {
          errs() << *var << "\n";
        }
      }
    }
    errs() << "\n";
  }
  void printInAndOut(Function &F) {
    errs() << "Function \"" << F.getName() << "\" \n";
    for (auto &I : instructions(F)) {
      errs() << "INSTRUCTION: " << I << '\n';
      errs() << "***************** IN\n{\n";
      auto in = IN[&I];
      for (uint i = 0; i < in.size(); ++i) {
        if (in[i]) {
          errs() << " " << *labelValue[i] << "\n";
        }
      }
      errs() << "}\n**************************************\n***************** "
                "OUT\n{\n";
      auto out = OUT[&I];
      for (uint i = 0; i < out.size(); ++i) {
        if (out[i]) {
          errs() << " " << *labelValue[i] << "\n";
        }
      }
      errs() << "}\n**************************************\n\n\n\n";
    }
  }
  void printSet() {
    for (auto &k : valueLabel) {
      auto tmp = k.first;
      errs() << *tmp << "  " << k.second << "\n";
      errs() << "IN:";
      printBit(IN[tmp]);
      errs() << "OUT:";
      printBit(OUT[tmp]);
      errs() << "GEN:";
      printBit(GEN[tmp]);
      errs() << "KILL:";
      printBit(KILL[tmp]);
    }
  }
  void printMustAlias() {
    errs() << "mustAlias:"
           << "\n";
    for (auto &k : mustAlias) {
      errs() << *labelValue[k.first] << ":\n";
      printBit(k.second);
      for (uint i = 0; i < k.second.size(); ++i) {
        if (k.second[i] == true && !ssaVarDel[i]) {
          // errs()<<*labelValue[i]<<" "<<valueLabel[labelValue[i]]<<"\n";
          if (labelValue[i] != nullptr)
            errs() << labelValue[i] << " " << *labelValue[i] << " "
                   << valueLabel[labelValue[i]] << "\n";
          else
            errs() << valueLabel[labelValue[i]] << "\n";
        }
      }
      errs() << "\n";
    }
  }
  void printBit(BitVector tmp) {
    for (uint i = 0; i < tmp.size(); ++i) {
      errs() << (tmp[i] ? "1" : "0");
    }
    errs() << "\n";
  }
  void printVar() {
    for (auto &k : valueLabel) {
      if (k.first)
        errs() << k.second << "  " << *k.first << "\n";
      else
        errs() << k.second << "\n";
    }
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AAResultsWrapperPass>();
    AU.setPreservesAll();
  }
};
} // namespace

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT *_PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
                                        [](const PassManagerBuilder &,
                                           legacy::PassManagerBase &PM) {
                                          if (!_PassMaker) {
                                            PM.add(_PassMaker = new CAT());
                                          }
                                        }); // ** for -Ox
static RegisterStandardPasses
    _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
              [](const PassManagerBuilder &, legacy::PassManagerBase &PM) {
                if (!_PassMaker) {
                  PM.add(_PassMaker = new CAT());
                }
              }); // ** for -O0
