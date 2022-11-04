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
#define func_name getCalledFunction()->getName()
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
    unordered_map<CallInst*, int> last_int;
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
            if(isa<CallInst>(phi->getIncomingValue(i))) {
              label_set[inst_label[cast<CallInst>(phi->getOperand(i))]] |= inst_bitvector[inst];
            }
          }
        } else if(isa<CallInst>(first_Op) && cast<CallInst>(first_Op)->func_name == "CAT_new") {
            auto origin_inst = cast<Instruction>(inst->getArgOperand(0));
            label_set[inst_label[origin_inst]] |= inst_bitvector[inst];
        }
      } else if(fun_name != "CAT_get"){ //arbitrary function
        unsigned n = inst->getNumOperands();
        for(unsigned i = 0; i < n; i++) {
          auto op = inst->getOperand(i);
          if(isa<CallInst>(op) && CAT_Function.count(cast<CallInst>(op)->func_name)) {
            auto cat_inst = cast<CallInst>(op);
            if(cat_inst->func_name == "CAT_new") {
              label_set[inst_label[cat_inst]] |= inst_bitvector[inst];
            } else if(CAT_Function.count(cat_inst->func_name)) {
              auto cat_new = dyn_cast<CallInst>(cat_inst->getOperand(0));
              if(cat_new && cat_new->func_name == "CAT_new") {
                label_set[inst_label[cat_new]] |= inst_bitvector[inst];
              }
            }
          }
        }
      }
    }

    void setGenAndKill(Instruction *inst) {
      StringRef fun_name;
      if(isa<CallInst>(inst)) fun_name = cast<CallInst>(inst)->getCalledFunction()->getName();
      else if(auto store_inst = dyn_cast<StoreInst>(inst)) {
        gen[inst] = BitVector(inst_count, false);
        kill[inst] = BitVector(inst_count, false);
        if(auto cat_cal = dyn_cast<CallInst>(store_inst->getValueOperand())) {
          if(cat_cal->func_name == "CAT_new") {
            //gen[inst] = inst_bitvector[cat_cal];
            //kill[inst] = label_set[inst_label[cat_cal]];
          }
        }
        return;
      } else if(auto load_inst = dyn_cast<LoadInst>(inst)) {
        gen[inst] = BitVector(inst_count, false);
        kill[inst] = BitVector(inst_count, false);
        if(auto cat_cal = dyn_cast<CallInst>(load_inst->getPointerOperand())) {
          if(cat_cal->func_name == "CAT_new") {
            gen[inst] = label_set[inst_label[cat_cal]];
          } else {
            AliasAnalysis &aa = getAnalysis<AAResultsWrapperPass>().getAAResults();
            for(auto &instr : instructions(inst->getFunction())) {
              if(auto cal_cat = dyn_cast<CallInst>(&instr)) {
                if(cal_cat->func_name == "CAT_new") {
                  switch(aa.alias(inst, cal_cat)) {
                    case AliasResult::MustAlias:
                    case AliasResult::MayAlias:
                      gen[inst] |= inst_bitvector[cal_cat];
                      break;
                    default:
                      break;
                  }
                }
              }
            }
          }
        }
        return;
      }else {
        gen[inst] = BitVector(inst_count, false);
        kill[inst] = BitVector(inst_count, false);
        return;
      }
      BitVector bit_vec(inst_count, false); 
      if(fun_name == "CAT_new") {
        bit_vec = label_set[inst_label[inst]];
        gen[inst] = inst_bitvector[inst];
      } else if(CAT_Function.count(fun_name)) {
        auto cat_new = inst->getOperand(0);
        if(auto phi = dyn_cast<PHINode>(cat_new)) {
          //bit_vec |= inst_bitvector[inst];
          for(unsigned i = 0; i < phi->getNumOperands(); i++) {
            auto cat_new = phi->getOperand(i);
            if(auto call_new = dyn_cast<CallInst>(cat_new)) {
              bit_vec |= label_set[inst_label[call_new]];
            } 
          }
        } else if(isa<CallInst>(inst->getOperand(0))) {
          CallInst *cal_inst = cast<CallInst>(inst->getOperand(0));
          bit_vec = label_set[inst_label[cal_inst]];
        }
        gen[inst] = inst_bitvector[inst];
      } else {
        gen[inst]  = BitVector(inst_count, 0);
      }
      if(CAT_Function.count(fun_name)) {
        bit_vec ^= inst_bitvector[inst];
        kill[inst] = bit_vec;
      } else if(fun_name == "CAT_get") {
        kill[inst] = BitVector(inst_count, false);
      } else {
        kill[inst] = BitVector(inst_count, false);
        for(unsigned i = 0; i < inst->getNumOperands(); i++) {
          if(auto cat_inst = dyn_cast<CallInst>(inst->getOperand(i))) {
            if(cat_inst->func_name == "CAT_new") {
              auto cat_fun = dyn_cast<CallInst>(inst)->getCalledFunction();
              for(auto &sub_inst : instructions(cat_fun)) {
                if(auto sub_call = dyn_cast<CallInst>(&sub_inst)) {
                  if(CAT_Function.count(sub_call->func_name) && sub_call->func_name != "CAT_new") {
                    if(sub_call->getOperand(0) == cat_fun->getArg(i)) {
                      kill[inst] |= label_set[inst_label[cat_inst]];
                    }
                  }
                }
              }
            }
          } else if(isa<PointerType>(inst->getOperand(i)->getType()) && isa<Instruction>(inst->getOperand(i))) {
            AliasAnalysis &aa = getAnalysis<AAResultsWrapperPass>().getAAResults();
            auto inst_func = cast<CallInst>(inst)->getCalledFunction();
            bool will_mod = 0;
            for(auto &inst_fun : instructions(inst_func)) {
              if(auto cat_call = dyn_cast<CallInst>(&inst_fun)) {
                errs() << "CALL: " << *cat_call << "\n";
                if(CAT_Function.count(cat_call->func_name) && cat_call->func_name != "CAT_new") {
                  for(auto it = inst_func->getArg(i)->user_begin(); it != inst->getOperand(i)->user_end(); it++) {
                    errs() << **it  << "\n";
                    errs() << (int) aa.alias(cat_call->getOperand(0), *it) << "\n";
                    switch(aa.alias(cat_call->getOperand(0), *it)) {
                      case AliasResult::MustAlias:
                        will_mod = 1;
                        break;
                      default:
                        break;
                    }
                    errs() << "will_mod" << will_mod << "\n";
                  }
                  
                }
              }
            }
            for(auto &inst_c : instructions(inst->getFunction())) {
              if(isa<StoreInst>(&inst_c)) {
                errs() << inst_c << "\n";
                errs() << *inst << "\n";
                errs() << (int)aa.getModRefInfo(dyn_cast<CallInst>(inst), cast<StoreInst>(&inst_c), 8) << "\n\n\n";
                switch(aa.getModRefInfo(dyn_cast<Instruction>(inst), cast<StoreInst>(&inst_c), 8)) {
                  case ModRefInfo::ModRef:
                  case ModRefInfo::Mod:
                  case ModRefInfo::MustMod:
                  case ModRefInfo::MustModRef:
                    if(will_mod == 1) {
                      errs() << cast<StoreInst>(&inst_c)->getValueOperand() << "\n";
                      kill[inst] |= label_set[inst_label[cast<Instruction>(cast<StoreInst>(&inst_c)->getValueOperand())]];
                    }
                    break;
                  default:
                    break;
                }
              }
            }
          }
        }
      }
    }

    
    void setInAndOut(Function &F) {

      for(auto &inst : instructions(F)) {
          setGenAndKill(&inst);
      }
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
        auto in_bit = in[&inst]; 
        errs() << "INSTRUCTION: " << inst << "\n";
        errs() << "***************** IN\n{\n";
        for(unsigned i = 0; i < inst_count; i++) {
          if(in_bit[i] == true) errs() << " " << *label_inst[i] << "\n";
        }
        errs() << "}\n**************************************\n";
        errs() << "***************** OUT\n{\n";
        auto out_bit = out[&inst];
        for(unsigned i = 0; i < inst_count; i++) {
          if(out_bit[i] == true) errs() << " " << *label_inst[i] << "\n";
        }
        errs() << "}\n**************************************\n\n\n\n";
      }
    }

    void optimizeFunction(Function &F) {
      queue<CallInst*> work_list;
      for(auto &inst : instructions(F)) {
        if(auto cal_inst = dyn_cast<CallInst>(&inst)) {
          work_list.push(cal_inst);
        }
      }
      if(work_list.empty()) return;
      vector<BasicBlock*> bb_list;
      unordered_set<CallInst*>del_list;
      do {
        auto cal_inst = work_list.front();
        work_list.pop();
        genInAndOut(F);
        aliasOptimize(F);
        StringRef f_name = cal_inst->func_name;
        if(f_name == "CAT_get" && isa<CallInst>(cal_inst->getOperand(0))) {
          auto d1 = cast<CallInst>(cal_inst->getOperand(0));
          BitVector in1 = in[cal_inst], d1_set = label_set[inst_label[d1]];
          d1_set &= in1;
          unordered_set<ConstantInt*> result_set;
          int in_count = 0;
          for(unsigned i = 0; i < d1_set.size(); i++) {
            if(d1_set[i] == 1) in_count++;
          }
          for(unsigned i = 0; i < d1_set.size(); i++) {
            if(d1_set[i] == 1) {
              StringRef name = dyn_cast<CallInst>(label_inst[i])->func_name;
              if(name == "CAT_new") {
                auto result = dyn_cast<ConstantInt>(label_inst[i]->getOperand(0));
                if(result) {
                   result_set.insert(result);
                   in_count--;
                } 

              } else if(name == "CAT_add" || name == "CAT_sub") {
                if(isa<ConstantInt>(label_inst[i]->getOperand(1)) && isa<ConstantInt>(label_inst[i]->getOperand(2))) {
                  if(name == "CAT_add") {
                    auto const1 = cast<ConstantInt>(label_inst[i]->getOperand(1))->getSExtValue();
                    auto const2 = cast<ConstantInt>(label_inst[i]->getOperand(2))->getSExtValue();
                    auto result = ConstantInt::get(IntegerType::get(F.getParent()->getContext(), 32), const1 + const2);
                    result_set.insert(result);
                    in_count--;

                    
                  } else {
                    auto const1 = cast<ConstantInt>(label_inst[i]->getOperand(1))->getSExtValue();
                    auto const2 = cast<ConstantInt>(label_inst[i]->getOperand(2))->getSExtValue();
                    auto result = ConstantInt::get(IntegerType::get(F.getParent()->getContext(), 32), const1 - const2);
                    result_set.insert(result);
                    in_count--;
                    
                  }
                } 
              } else if(name == "CAT_set") {
                if(isa<ConstantInt>(label_inst[i]->getOperand(1))) {
                  auto result = dyn_cast<ConstantInt>(label_inst[i]->getOperand(1));
                  if(result) {
                    result_set.insert(result);
                    in_count--;
                  }

                }
              }
            }
          }
          if(result_set.size() == 1 && in_count == 0) {
              cal_inst->replaceAllUsesWith(*result_set.begin());
              cal_inst->eraseFromParent();
          }
        } else if(f_name == "CAT_get" && isa<PHINode>(cal_inst->getOperand(0))) {
          unordered_set<ConstantInt*> result_set;
          auto node = cast<PHINode>(cal_inst->getOperand(0));
          queue<PHINode*> node_list;
          node_list.push(node);
          errs() << "--------" << *node << "\n";
          while(!node_list.empty()) {
            auto phi_node = node_list.front();
            node_list.pop();
            for(auto it = phi_node->op_begin(); it != phi_node->op_end(); it++) {
              if(isa<PHINode>(*it)) node_list.push(cast<PHINode>(*it));
              else if(isa<CallInst>(*it)) {
                auto cat_cal = cast<CallInst>(*it);
                if(cat_cal->func_name == "CAT_new" && isa<ConstantInt>(cat_cal->getOperand(0))) {
                  errs() << "the constant" << *cat_cal->getOperand(0) << "\n";
                  result_set.insert(cast<ConstantInt>(cat_cal->getOperand(0)));
                }
              } else if(isa<ConstantInt>(*it)) result_set.insert(cast<ConstantInt>(*it));
              else goto fail;
            }
          }
          errs() << "Done, no fail!" << "\n";
          for(auto it = cal_inst->user_begin(); it != cal_inst->user_end(); it++) {
            BitVector in_bit = in[dyn_cast<CallInst>(*it)];
            in_bit &= in[node];
            if(in_bit == in[node] && result_set.size() == 1) {
              errs() << "replace : " << *cal_inst << '\n';
              errs() << **it << " " << **result_set.begin() << "\n";
              it->replaceUsesOfWith(cal_inst, *result_set.begin());
              del_list.insert(cal_inst);
            }
          }
          //to be modify
          /***
          unsigned in_count = 0;
          for(unsigned i = 0 ; i < phi_node->getNumOperands(); i++) {
            if(isa<ConstantInt>(phi_node->getIncomingValue(i))) {
              result_set.insert(cast<ConstantInt>(phi_node->getIncomingValue(i)));
              in_count++;
            } 
          }
          
          if(result_set.size() == 1 && node->getNumOperands() == in_count) {
            phi_node->replaceAllUsesWith(*result_set.begin());
          }
          **/ 
        fail:
          ;
        } else if((f_name == "CAT_add" || f_name == "CAT_sub")) {
          auto v1 = cal_inst->getOperand(1), v2 = cal_inst->getOperand(2);
          unordered_set<ConstantInt*> const_num1, const_num2;
          int in_count1 = 0, in_count2 = 0;
          if(auto d1 = dyn_cast<CallInst>(v1)) {
            BitVector in1 = in[cal_inst], d1_set = label_set[inst_label[d1]];
            d1_set &= in1;
            for(unsigned i = 0; i < inst_count; i++) {
              if(d1_set[i] == 1) in_count1++;
            }
            for(unsigned i  = 0; i < inst_count; i++) {
              if(d1_set[i] == 1) {
                StringRef name = dyn_cast<CallInst>(label_inst[i])->func_name;
                if(name == "CAT_new" && isa<ConstantInt>(label_inst[i]->getOperand(0))) {
                  const_num1.insert(cast<ConstantInt>(label_inst[i]->getOperand(0)));
                  in_count1--;
                } else if(name == "CAT_set" && isa<ConstantInt>(label_inst[i]->getOperand(1))) {
                  const_num1.insert(cast<ConstantInt>(label_inst[i]->getOperand(1)));
                  in_count1--;
                } 
              }
            }
          }
          if(auto d2 = dyn_cast<CallInst>(v2)) {
            BitVector in2 = in[cal_inst], d2_set = label_set[inst_label[d2]];
            d2_set &= in2;
            for(unsigned i = 0; i < inst_count; i++) {
              if(d2_set[i] == 1) in_count2++;
            }
            for(unsigned i = 0; i < inst_count; i++) {
              if(d2_set[i] == 1) {
                StringRef name = dyn_cast<CallInst>(label_inst[i])->func_name;
                if(name == "CAT_new" && isa<ConstantInt>(label_inst[i]->getOperand(0))) {
                  const_num2.insert(cast<ConstantInt>(label_inst[i]->getOperand(0)));
                  in_count2--;
                } else if(name == "CAT_set" && isa<ConstantInt>(label_inst[i]->getOperand(1))) {
                  const_num2.insert(cast<ConstantInt>(label_inst[i]->getOperand(1)));
                  in_count2--;
                }
              }
            }
            
          }
          if(const_num1.size() == 1 && const_num2.size() == 1 && in_count1 == 0 && in_count2 == 0)  {
              Value* result;
              IRBuilder<> builder(cal_inst);
              if(f_name == "CAT_add") {
                result = builder.CreateAdd(*const_num1.begin(), *const_num2.begin());
              } else {
                result = builder.CreateSub(*const_num1.begin(), *const_num2.begin());
              }
              auto call = builder.CreateCall(F.getParent()->getFunction("CAT_set"), {
                cal_inst->getOperand(0),
                result
              });
              dyn_cast<CallInst>(call)->setTailCall();
              cal_inst->eraseFromParent();
          } else if(v1 == v2 && f_name == "CAT_sub") {
            Value *result =  ConstantInt::get(IntegerType::get(F.getParent()->getContext(), 64), 0);
            IRBuilder<> builder(cal_inst);
            auto call = builder.CreateCall(F.getParent()->getFunction("CAT_set"), {
                cal_inst->getOperand(0),
                result
            });
            dyn_cast<CallInst>(call)->setTailCall();
            cal_inst->eraseFromParent();
          }
        } /**else if(f_name == "CAT_set") {
          Instruction* prev_inst = cal_inst->getPrevNode();
          if(prev_inst) {
            while(prev_inst && isa<CallInst>(prev_inst)) {
              if(CAT_Function.count(cast<CallInst>(prev_inst)->func_name) && prev_inst->getOperand(0) == cal_inst->getOperand(0)) {
                del_list.insert(cast<CallInst>(prev_inst));
                prev_inst = prev_inst->getPrevNode();
              } else {
                break;
              }
            }
          }
        }**/
        queue<PHINode*> phi_list;
        for(auto &inst : instructions(F)) {
          if(auto phi_node = dyn_cast<PHINode>(&inst)) {
            phi_list.push((phi_node));
          }
        }
        while(!phi_list.empty()) {
          genInAndOut(F);
          auto inst = phi_list.front();
          phi_list.pop();
          if(auto phi_node = dyn_cast<PHINode>(inst)) {
            if(phi_node->getNumOperands() == 1 && isa<ConstantInt>(phi_node->getIncomingValue(0))) {
              phi_node->setOperand(0, cast<ConstantInt>(phi_node->getIncomingValue(0)));
            } else if(phi_node->getNumOperands() == 1 && isa<CallInst>(phi_node->getIncomingValue(0))) {
              auto cal = cast<CallInst>(phi_node->getIncomingValue(0));
              if(cal->func_name == "CAT_new") {
                //phi_node->replaceAllUsesWith(cal);// to be deleted, iterate all use and modify if in_set has new
                BitVector phi_bit = BitVector(inst_count, 0);
                for(unsigned i  = 0; i < phi_node->getNumOperands(); i++) {
                  if(isa<CallInst>(phi_node->getIncomingValue(i)))
                    phi_bit |= inst_bitvector[cast<CallInst>(phi_node->getIncomingValue(i))];
                }
                for(auto it = phi_node->user_begin(); it != phi_node->user_end(); it++)  {
                  BitVector in_set = in[dyn_cast<CallInst>(*it)];
                  in_set &= phi_bit;
                  if(in_set != BitVector(inst_count, 0)) {
                    it->replaceUsesOfWith(phi_node, cal);
                  }
                  if(isa<PHINode>(*it)) {
                    it->replaceUsesOfWith(phi_node, cal);
                  }
                }
              } 
            }
            
            unordered_set<ConstantInt*> result_set;
            unsigned cnt = 0;
            for(unsigned i = 0; i < phi_node->getNumOperands(); i++) {
              if(auto cat_cal =dyn_cast<CallInst>(phi_node->getOperand(i))) {
                if(cat_cal->func_name == "CAT_new" && isa<ConstantInt>(cat_cal->getOperand(0))) {
                  result_set.insert(cast<ConstantInt>(cat_cal->getOperand(0)));
                  cnt++;
                }
              }
            } 
            if(result_set.size() == 1 && cnt == phi_node->getNumOperands()) {
              for(auto user = phi_node->user_begin(); user != phi_node->user_end(); user++) {
                auto cat_cal = dyn_cast<CallInst>(*user);
                if(cat_cal && cat_cal->func_name == "CAT_get") {
                  BitVector in_bit = in[cat_cal], phi_bit = in[phi_node];
                  if(in_bit == phi_bit) {
                    vector<Value*> use_list;
                    for(auto u : user->users()) {
                      use_list.push_back(u);
                      //(*u).setOperand(1, *result_set.begin());
                      //u.getUser()->replaceUsesOfWith(*user, *result_set.begin());
                    }
                    for(auto u : use_list) {
                      dyn_cast<CallInst>(u)->setOperand(1, *result_set.begin());
                      del_list.insert(cast<CallInst>(cat_cal));
                    }
                  }
                }
              }
            }
          }
        }
      } while(!work_list.empty());
      for(auto i : del_list) i->eraseFromParent();
      genInAndOut(F);
    }
    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    void genInAndOut(Function &F) {
      label_inst.clear();
      inst_label.clear();
      label_set.clear();
      inst_bitvector.clear();
      inst_count = 0;
      in.clear();
      out.clear();
      gen.clear();
      kill.clear();
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
      setInAndOut(F);
    }

    void aliasOptimize(Function &F) {
      AliasAnalysis &aa = getAnalysis<AAResultsWrapperPass>().getAAResults();
      vector<Instruction*> del_list;
      for(auto &inst : instructions(F)) {
        auto cal_inst = dyn_cast<CallInst>(&inst);
        if(cal_inst && cal_inst->func_name == "CAT_get") {
          for(auto &[inst_id, bit] : label_set) {
            auto cat_new = dyn_cast<CallInst>(label_inst[inst_id]);
            BitVector in_bit = in[cal_inst], cat_bit = inst_bitvector[cat_new];
            switch(cat_new && aa.alias(cat_new, cal_inst->getOperand(0)) && cat_new->func_name == "CAT_new") {
              case llvm::AliasResult::MustAlias:
                in_bit &= cat_bit;
                if(in_bit != BitVector(inst_count, 0)) {
                  errs() << *cal_inst << "\n-----" << *cat_new << "\n";
                  cal_inst->replaceAllUsesWith(cat_new->getOperand(0));
                  del_list.push_back(cal_inst);
                }
                break;
              default:
                break;
            }
          }
        }
      }
      for(auto &val : del_list) val->eraseFromParent();
    }

    bool runOnFunction (Function &F) override {
      genInAndOut(F);
      optimizeFunction(F);
      printInAndOut(F);
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
