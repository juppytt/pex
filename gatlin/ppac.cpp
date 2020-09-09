#include "ppac.h"
#include "utility.h"
using namespace llvm;

extern cl::opt<string> knob_crit_struct_list;

char ppac::ID;
///////////////////////////////////////////////////////////////////////////

// Backward analysis of privileged gep instruction usage.
GEP_TYPE ppac::find_gep_type(GetElementPtrInst *gi, bool dbg,
                             DominatorTree *dt, InstructionSet *chk_set)
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
            chk_set->insert(cast<Instruction>(v));

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

GEP_TYPE ppac::is_interesting_gep(GetElementPtrInst *gi, DominatorTree *dt, InstructionSet *chk_set)
{
    Type *gty = gi->getSourceElementType();
    StructType *sty = dyn_cast<StructType>(gty);
    if (!sty)
        return UNPRIV;
    if (!crit_structs->exists(sty->getName()))
        return UNPRIV;

    return find_gep_type(gi, false, dt, chk_set);

}
void ppac::process_ppac(Module &module)
{
    for (Module::iterator fi = module.begin(), fe = module.end();
         fi != fe; ++fi)
    {
        Function *func = dyn_cast<Function>(fi);
        if (!func)
            continue;
        if (func->isDeclaration() || func->isIntrinsic() || (!func->hasName()))
            continue;
        InstructionSet *chk_set = f2di[func];
        if (chk_set == NULL){
            chk_set = new InstructionSet;
            f2di[func] = chk_set;
        }
        DominatorTree dt(*func);
        AliasAnalysis *aa = &getAnalysis<AAResultsWrapperPass>(*func).getAAResults();
        MemorySSA mssa(*func, aa, &dt);

        errs() << "MemorySSA\n";
        mssa.dump();
        errs() << "\n";

        collect_privileged_instructions(func, &dt, chk_set);
        collect_internal_source_type(func, chk_set, &dt, &mssa, aa);

    }

    dump_i2ty();
}
// priv. struct type gep - ld/st
// priv. struct pointer type ld/st
void ppac::collect_privileged_instructions(Function *func, DominatorTree *dt, InstructionSet *chk_set)
{
    for (Function::iterator bi = func->begin(), be = func->end();
         bi != be; ++bi) {
        BasicBlock* bb = dyn_cast<BasicBlock>(bi);
        for (BasicBlock::iterator ii = bb->begin(), ie = bb->end();
             ii != ie; ++ii)
        {
            GetElementPtrInst *gi = dyn_cast<GetElementPtrInst>(ii);
            if (!gi)
                continue;
            GEP_TYPE gep_ty = is_interesting_gep(gi, dt, chk_set);
            switch(gep_ty) {
                case UNPRIV:
                    continue;
                case PRIV_ETC:
                    find_gep_type(gi, true, dt, chk_set);
                    continue;
                case LOAD:
                case STORE:
                    //collect_internal_source_type(gi, is, dt, &mssa);
                default:
                    continue;
            }
        }
    }
}

void ppac::collect_internal_source_type(Function *func, InstructionSet *chk_set,
                                        DominatorTree *dt, MemorySSA *mssa,
                                        AliasAnalysis *aa) {

    for (auto ii : *chk_set) {
        _collect_internal_source_type(ii, chk_set, dt, mssa, aa);
    }
}

void ppac::_collect_internal_source_type(Instruction *ii,
                                         InstructionSet *chk_set,
                                         DominatorTree *dt,
                                         MemorySSA *mssa,
                                         AliasAnalysis *aa) {
    TypeSet *ts = i2ty[ii];
    ValueSet *vs_local = i2vl_local[ii];
    ValueSet *vs_trans = i2vl_trans[ii];
    if (!ts){
        ts = new TypeSet;
        vs_local = new ValueSet;
        vs_trans = new ValueSet;
        i2ty[ii] = ts;
        i2vl_local[ii] = vs_local;
        i2vl_trans[ii] = vs_trans;
    }

    MemoryUseOrDef *ma = mssa->getMemoryAccess(ii);
    if (isa<MemoryUse>(ma)) {
        Instruction *usei = cast<MemoryUse>(ma)->getMemoryInst();
        if (!usei) {
            if (isa<StoreInst>(usei)) {
                __collect_internal_source_type(ts,
                    cast<Instruction>(cast<StoreInst>(usei)->getPointerOperand()), chk_set, dt, mssa, aa);
            }
        }
    }

    Instruction *srci;
    if (isa<LoadInst>(ii)) {
        LoadInst *li = dyn_cast<LoadInst>(ii);
        srci = dyn_cast<Instruction>(li->getPointerOperand());
        if (!srci)
            return;
    }
    else if (isa<StoreInst>(ii)) {
        StoreInst *si = dyn_cast<StoreInst>(ii);
        srci = dyn_cast<Instruction>(si->getPointerOperand());
        if (!srci)
            return;
    }
    else
        return;
    __collect_internal_source_type(ts, srci, chk_set, dt, mssa, aa);
}

void ppac::__collect_internal_source_type(TypeSet *ts,
                                         Instruction *srci,
                                         InstructionSet *chk_set,
                                         DominatorTree *dt,
                                         MemorySSA *mssa,
                                         AliasAnalysis *aa) {

    InstructionSet visited;
    InstructionList worklist;
    InstructionList uselist;
    bool cast = false;
    Type *curr_ty = srci->getType();
    worklist.push_back(srci);
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

        if (isa<GetElementPtrInst>(v) || isa<CastInst>(v)) {
            Value *u = (dyn_cast<Instruction>(v))->getOperand(0);
            Instruction *ui = dyn_cast<Instruction>(u);
            if (!ui)
                continue;
            worklist.push_front(ui);
            if (isa<CastInst>(v))
                cast = true;
            if (isa<GetElementPtrInst>(v))
                curr_ty = dyn_cast<GetElementPtrInst>(v)->getPointerOperandType();
            continue;
        }

        // data structure stored in stack
        if (isa<AllocaInst>(v)) {
            // TODO: Let's ignore stack object dereference.
            ts->insert(nullptr);
            continue;
        }

        if (isa<LoadInst>(v)) {
            LoadInst *li = dyn_cast<LoadInst>(v);

            if (chk_set->count(li)) {
                // This load is also a privilegd instruction.
                // We can use the analysis result of this instruction.
                _collect_internal_source_type(li, chk_set, dt, mssa, aa);
                TypeSet *link_tys = i2ty[li];
                if (!link_tys) {
                    errs () << "No analysis result from parent?\n";
                    continue;
                }
                if (!cast) {
                    // There was no cast. We can use this type result directly.
                    if (link_tys->size() == 0) {
                        if (i2vl_trans[li]->size() == 0) {
                        errs() << "    " << *li << "\n";
                        errs() << "    : No source type found?\n";
                        }
                        // let's hope we can get soruce by inter-function analysis
                        continue;
                    } else{
                        Type *parent_ty = li->getType();

                        // check if there is other type used.
                        // for now, print other types.
                        for (auto psty : *link_tys) {
                            if (psty == nullptr)
                                errs() << "Parent source type: stack obj\n";
                            else if (psty != parent_ty)
                                errs() << "Parent source type: " << *psty << "\n";
                        }
                        errs() << "we got parent analysis\n";
                        errs() << "parent: " << *li << "\n";
                        errs() << "curr_ty: " << *curr_ty << "\n";
                        if (is_parent_like_type(curr_ty, parent_ty))
                            ts->insert(curr_ty);
                        continue;
                    }
                }

                else {
                    // TODO: type cast between our dereference and this load.
                    continue;
                }
            }

            // This load is not priivleged type...
            Value *src = li->getPointerOperand();
           
            // it is using data pointer stored in stack.
            // this includes function arguments
            if (isa<AllocaInst>(src)) {
                find_stack_src_ty(dyn_cast<LoadInst>(v), ts, dt, mssa);
                continue;
            }

            if (isa<GetElementPtrInst>(src)) {
                // TODO: Non privileged GEP instruction?
                GetElementPtrInst *gsrc = dyn_cast<GetElementPtrInst>(src);
                Type *parent_ty = gsrc->getSourceElementType();
                errs() << "Why non privilegd GEP?\n";
                errs() << *gsrc << "\n";
                //TODO: getelementptr array type
                if (isa<ArrayType>(parent_ty)) {
                    continue;
                }
                if (isa<StructType>(parent_ty))
                    continue;
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

    MemoryAccess *ma = mssa->getWalker()->getClobberingMemoryAccess(li);
    //MemoryUseOrDef *muod = mssa->getMemoryAccess(li);
    //errs() << "Load: " << *li << "\n";
    //errs() << "Muod: " << *muod << "\n";
    //errs() << "Clob: " << *ma << "\n";

    if (isa<MemoryDef>(ma)) {
        find_src_ty(dyn_cast<MemoryDef>(ma), ts);
    }
    else if (isa<MemoryPhi>(ma)){
        MemoryPhi *mphi = dyn_cast<MemoryPhi>(ma);
        errs() << "MPhi incoming values:\n";
        for (int i=0; i<mphi->getNumIncomingValues(); i++)
        {
            MemoryAccess *in = mphi->getIncomingValue(i);
            errs() << "  " << *in << "\n";
            if (isa<MemoryDef>(in))
                find_src_ty(dyn_cast<MemoryDef>(in), ts);
        }
    }

}
void ppac::find_src_ty(MemoryDef *def, TypeSet *ts)
{
    Instruction *defi = def->getMemoryInst();
    StoreInst *defsi = dyn_cast<StoreInst>(defi);
    if (!defsi) {
        errs() << "Closest definition is not store?\n    " << *defi << "\n";
        return;
    }

    errs() << "find_src_ty\n";
    errs() << *defsi << "\n";
    Value *stval = defsi->getValueOperand();
    ValueList worklist;
    worklist.push_back(stval);
    Type *cast_ty = nullptr;
    while(worklist.size()) {
        Value *v = worklist.front();
        worklist.pop_front();
        errs() << "  " << *v << "\n";
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
        if (isa<LoadInst>(v)) {
            worklist.push_back(cast<LoadInst>(v)->getPointerOperand());
            continue;
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

bool ppac::is_elem_ptr(Type *child, Type *parent) {
    if (child == parent)
        return true;

    Type *strip_ty = parent;

    while(true) {
        PointerType *strip_ptr = dyn_cast<PointerType>(strip_ty);
        if (!strip_ptr)
            break;
        strip_ty = strip_ptr->getElementType();
        if (child == strip_ty)
            return true;
    }
    return false;
}

bool ppac::is_elem_struct(Type *child, Type *parent) {
    Type *strip_ty = parent;

    StructType *parent_str = dyn_cast<StructType>(strip_ty);
    if (!parent_str)
        return false;

    for (auto elem : parent_str->elements()) {
        if (is_elem_ptr(child, elem))
            return true;
        if (isa<StructType>(elem)) {
            if (is_elem_struct(child, elem))
                return true;
        }
    }
    return false;
}
bool ppac::is_parent_like_type(Type *child, Type *parent) {
    if (is_elem_ptr(child, parent))
        return true;
    if (is_elem_struct(child, parent))
        return true;
    return false;
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
            if (ty == nullptr)
                errs() << "stack obj, ";
            else
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
    process_ppac(module);
}

static RegisterPass<ppac>
XXX("ppac", "ppac Pass");
