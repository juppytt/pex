#ifndef __PPAC_H_
#define __PPAC_H_

#include "llvm-c/Core.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemorySSA.h"
#include "commontypes.h"

#include "simple_set.h"
#include "internal.h"
#include "utility.h"

#define DEBUG_TYPE "ppac"

enum GEP_TYPE {
LOAD,
STORE,
CAST,
EXT,
PRIV_ETC,
UNPRIV
};

class ppac : public ModulePass
{
private:
    virtual bool runOnModule(Module&) override;
    virtual bool doInitialization(Module&) override;
    virtual void getAnalysisUsage(AnalysisUsage&) const override;
    bool ppacPass(Module&);

    void process_ppac(Module&);
    GEP_TYPE is_interesting_gep(GetElementPtrInst*, DominatorTree*, InstructionSet*);
    void collect_privileged_instructions(Function*, DominatorTree*, InstructionSet*);
    void collect_internal_source_type(Function*, InstructionSet*,
                                      DominatorTree*, MemorySSA*);
    void _collect_internal_source_type(Instruction*, InstructionSet*,
                                       DominatorTree*, MemorySSA*);

    GEP_TYPE find_gep_type(GetElementPtrInst*, bool, DominatorTree*, InstructionSet*);
    void find_stack_src_ty(LoadInst*, TypeSet*, DominatorTree*, MemorySSA*);
    void check_cast_usage(GetElementPtrInst*);
    void initialize_alloc_funcs();
    void print_gep_usage(GetElementPtrInst*);
    void print(InstructionList&);
    void dump_i2ty();
    void dump_i2vl();
public:
    static char ID;
    ppac() : ModulePass(ID) {};

    virtual StringRef getPassName() const override
    {
        return "ppac";
    }
private:
    LLVMContext *ctx;
    Module *m;
   
    StructTypeSet priv_types;
    //map function to its dereferent instruction
    Function2ChkInst f2di;

    //map instruction to accessible types
    Inst2Type i2ty;
    //map instruction to accessible initial value (allocation site)
    //values defined in function, collected by intra-function analysis
    Inst2Val i2vl_local;
    //values defined out of the function, collected by inter-function analysis
    Inst2Val i2vl_external;
    //values that contain external sources (internal usage of external sources)
    Inst2Val i2vl_trans;
    StringSet alloc_funcs;

};

#endif // __PPAC_H_
