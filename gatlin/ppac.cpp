#include "ppac.h"
#include "utility.h"
using namespace llvm;

extern cl::opt<string> knob_crit_struct_list;

char ppac::ID;
///////////////////////////////////////////////////////////////////////////

GEP_TYPE ppac::find_gep_type(GetElementPtrInst *gi, bool dbg,
                             DominatorTree *dt)
{
    Function *func = gi->getFunction();


    GEP_TYPE res = PRIV_ETC;

    InstructionSet visited;
    InstructionList worklist;
    InstructionList uselist;
    worklist.push_back(gi);
    uselist.push_back(gi);


    while(worklist.size()) {
        Instruction *v = worklist.front();
        worklist.pop_front();

        if (visited.count(v))
            continue;

        while (uselist.size()) {
            Instruction *prev = uselist.back();
            if (!dt->dominates(prev, v))
                uselist.pop_back();
            else
                break;
        }
        uselist.push_back(v);


        if (isa<GetElementPtrInst>(v) || isa<CastInst>(v) || isa<BinaryOperator>(v)) {
            for (auto u : v->users()){
                Instruction *ui = dyn_cast<Instruction>(u);
                if (!ui)
                    continue;
                worklist.push_front(ui);
            }
            if (isa<CastInst>(v))
                res = CAST;
            continue;
        }
        if (isa<LoadInst>(v) || isa<StoreInst>(v)) {
            if (isa<LoadInst>(v))
                res = LOAD;
            else
                res = STORE;

            if (dbg){
                if (res == LOAD)
                    errs() << "LOAD:  ";
                else
                    errs() << "STORE: ";
                print(uselist);
            }
            uselist.pop_back();


            if (worklist.size()){
                errs() << "Worklist not empty\n";
                for (auto vv : worklist)
                    errs() << *vv << "\n";
            }
            return res;
        }
        if (isa<CallBase>(v) || isa<ReturnInst>(v)) {
            if (dbg) {
                errs() << "EXT:  ";
                print(uselist);
            }
            uselist.pop_back();
            res = EXT;
            if (worklist.size()){
                errs() << "Worklist not empty\n";
                for (auto vv : worklist)
                    errs() << *vv << "\n";
            }
            return res;
        }

        // what else?
        if (dbg){
            errs() << "Undefined: ";
            print(uselist);
        }

        uselist.pop_back();
    }
    return res;
}

GEP_TYPE ppac::is_interesting_gep(GetElementPtrInst *gi, DominatorTree *dt)
{
    Type *gty = gi->getSourceElementType();
    StructType *sty = dyn_cast<StructType>(gty);
    if (!sty)
        return UNPRIV;
    if (!crit_structs->exists(sty->getName()))
        return UNPRIV;

    return find_gep_type(gi, false, dt);

}

// TODO: Separate collect instructions / find source
void ppac::collect_privileged_instructions(Module &module)
{
    for (Module::iterator fi = module.begin(), fe = module.end();
         fi != fe; ++fi)
    {
        Function *func = dyn_cast<Function>(fi);
        if (!func)
            continue;
        if (func->isDeclaration() || func->isIntrinsic() || (!func->hasName()))
            continue;
        InstructionSet *is = f2di[func];
        if (is == NULL){
            is = new InstructionSet;
            f2di[func] = is;
        }
        DominatorTree dt(*func);
        AliasAnalysis *aa = &getAnalysis<AAResultsWrapperPass>(*func).getAAResults();
        MemorySSA mssa(*func, aa, &dt);

        //errs() << "MemorySSA\n";
        //mssa.dump();
        //errs() << "\n";
        for (Function::iterator bi = func->begin(), be = func->end();
             bi != be; ++bi)
        {
            BasicBlock* bb = dyn_cast<BasicBlock>(bi);
            for (BasicBlock::iterator ii = bb->begin(), ie = bb->end();
                 ii != ie; ++ii)
            {
                GetElementPtrInst *gi = dyn_cast<GetElementPtrInst>(ii);
                if (!gi)
                    continue;
                GEP_TYPE gep_ty = is_interesting_gep(gi, &dt);
                switch(gep_ty) {
                    case UNPRIV:
                        continue;
                    case PRIV_ETC:
                        find_gep_type(gi, true, &dt);
                        continue;
                    case LOAD:
                    case STORE:
                        collect_internal_source_type(gi, is, &dt, &mssa);
                    case CAST:
                        check_cast_usage(gi);
                }
            }
        }
    }
    dump_i2ty();
}

void ppac::collect_internal_source_type(GetElementPtrInst *gi, InstructionSet* is,
                                        DominatorTree *dt, MemorySSA *mssa) {
    if (is->count(gi))
        return;
    is->insert(gi);

    StructType *sty = dyn_cast<StructType>(gi->getSourceElementType());
    if (!sty) {
        errs() << "GEP is not struct type: \n    " << *gi << "\n";
        return;
    }
   
    TypeSet *ts = new TypeSet;
    i2ty[gi] = ts;

    ValueSet *vs_local = new ValueSet;
    ValueSet *vs_trans = new ValueSet;

    i2vl_local[gi] = vs_local;
    i2vl_trans[gi] = vs_trans;

    InstructionSet visited;
    InstructionList worklist;
    InstructionList uselist;
    worklist.push_back(gi);

    while(worklist.size()) {
        Instruction *v = worklist.front();
        worklist.pop_front();
        if (visited.count(v))
            continue;

        while(uselist.size()) {
            Instruction *next = uselist.front();
            if (!dt->dominates(v, next))
                uselist.pop_front();
            else
                break;
        }
        uselist.push_front(v);

        if (isa<GetElementPtrInst>(v) || isa<CastInst>(v) || isa<BinaryOperator>(v)) {
            for (Value *u : v->operands()) {
                Instruction *ui = dyn_cast<Instruction>(u);
                if (!ui)
                    continue;
                worklist.push_front(ui);
            }
            continue;
        }

        // data structure stored in stack
        if (isa<AllocaInst>(v)) {
            // Let's ignore stack object dereference.
            continue;
        }

        if (isa<LoadInst>(v)) {
            Value *src = cast<LoadInst>(v)->getPointerOperand();

            // it is using data pointer stored in stack.
            // this includes function arguments
            if (isa<AllocaInst>(src)) {
                find_stack_src_ty(cast<LoadInst>(v), ts, dt, mssa);
                continue;
            }

            if (isa<GetElementPtrInst>(src)) {
                GetElementPtrInst *gsrc = cast<GetElementPtrInst>(src);
                collect_internal_source_type(gsrc, is, dt, mssa);
                Type *parent_ty = gsrc->getSourceElementType();

                //TODO: getelementptr array type
                if (isa<ArrayType>(parent_ty)) {
                    continue;
                }
                if (!isa<StructType>(parent_ty))
                    continue;

                // whether or not parent struct is privileged type,
                // check if the source can be other type than the original parent type.
                collect_internal_source_type(gsrc, is, dt, mssa);
                TypeSet *link_tys = i2ty[gsrc];

                if (link_tys->size() == 0) {
                    if (i2vl_trans[gsrc]->size() == 0) {
                        errs() << "    " << *gsrc << "\n";
                        errs() << "    : No source type found?\n";
                    }
                    // let's hope we can get soruce by inter-function analysis
                    continue;
                } else {
                    // parent struct using parent type source!
                    if (link_tys->count(parent_ty))
                        ts->insert(sty);
                    // check if there is other type used.
                    // for now, print other types.
                    for (auto psty : *link_tys) {
                        if (psty != parent_ty)
                            errs() << "Parent used type: " << *psty << "\n";
                    }
                }
            }
        }
    }

}

void ppac::find_stack_src_ty(LoadInst *li, TypeSet *ts,
                             DominatorTree *dt, MemorySSA *mssa)
{
    Value *stack_ptr = li->getPointerOperand();
    Function *func = li->getFunction();
    StoreInst *src = NULL;

    /*for (auto u : stack_ptr->uses()){
        StoreInst *si = dyn_cast<StoreInst>(u);
        if (!si)
            continue;
        if (si->getPointerOperand() != stack_ptr)
            continue;
    }*/
    MemoryAccess *ma = mssa->getWalker()->getClobberingMemoryAccess(li);
    //MemoryUseOrDef *muod = mssa->getMemoryAccess(li);
    //errs() << "Load: " << *li << "\n";
    //errs() << "Muod: " << *muod << "\n";
    //errs() << "Clob: " << *ma << "\n";
    MemoryDef *def = dyn_cast<MemoryDef>(ma);
    if (!def) {
        errs() << "Cannot find def?\n    " << *li << "\n";
    }
    Instruction *defi = def->getMemoryInst();
    StoreInst *defsi = dyn_cast<StoreInst>(defi);
    if (!defsi) {
        errs() << "Closest definition is not store?\n    " << *defi << "\n";
    }

    Value *stval = defsi->getValueOperand();
    ValueList worklist;
    worklist.push_back(stval);
    Type *cast_ty = nullptr;
    while(worklist.size()) {
        Value *v = worklist.front();
        worklist.pop_front();
        if (isa<ConstantData>(v) || isa<GlobalValue>(v)) {
            ts->insert(v->getType());
            continue;
        }
        if (isa<CastInst>(v)) {
            worklist.push_back(cast<CastInst>(v)->getOperand(0));
            cast_ty = cast<CastInst>(v)->getDestTy();
            continue;
        }
        if (isa<CallBase>(v)) {
            Function *callee = cast<CallBase>(v)->getCalledFunction();
            if (alloc_funcs.count(callee->getName())) {
                // it allocated an object! insert allocated type.
                if (!cast_ty) {
                    errs() << "Weird... not casted?\n";
                    ts->insert(callee->getReturnType());
                    break;
                }
                ts->insert(cast_ty);
                break;
            }
        }
        if (isa<AllocaInst>(v)) {
            // Allocated stack object!
            ts->insert(cast<AllocaInst>(v)->getAllocatedType());
            break;
        }
        if (isa<Argument>(v)) {
            // TODO: need external analysis
            ts->insert(v->getType());
            break;
        }
    }


}
void ppac::check_cast_usage(GetElementPtrInst *gi)
{
   
}
void ppac::print(InstructionList &vl)
{
    for (auto v : vl) {
        errs() << *v;
        if (v != *vl.end())
            errs() << " => ";
        else
            errs() << "\n";
    }
    errs() << "\n\n";
}

void ppac::dump_i2ty() {
    for (auto iter : i2ty) {
        errs() << *(iter.first) << "\n";
        errs() << "  Types: ";
        for (auto ty : *(iter.second)) {
            errs() << *ty << ", ";
        }
        errs() <<"\n\n";
    }
}

void ppac::initialize_alloc_funcs() {
    alloc_funcs.insert("malloc");
}
bool ppac::doInitialization(Module &module)
{
    m = &module;
    initialize_crit_struct(knob_crit_struct_list);
    initialize_alloc_funcs();
}
bool ppac::runOnModule(Module &module)
{
    m = &module;
    return ppacPass(module);
}
void ppac::getAnalysisUsage(AnalysisUsage &AU) const
{
    AU.addRequired<AAResultsWrapperPass>();
}
bool ppac::ppacPass(Module &module)
{
    collect_privileged_instructions(module);
}

static RegisterPass<ppac>
XXX("ppac", "ppac Pass");
