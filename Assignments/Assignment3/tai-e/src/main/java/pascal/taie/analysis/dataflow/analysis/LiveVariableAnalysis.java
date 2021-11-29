/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2020-- Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2020-- Yue Li <yueli@nju.edu.cn>
 * All rights reserved.
 *
 * Tai-e is only for educational and academic purposes,
 * and any form of commercial use is disallowed.
 * Distribution of Tai-e is disallowed without the approval.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.List;
import java.util.Optional;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        return new SetFact<Var>();
        //return null;
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        //return null;
        return new SetFact<Var>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
        //target=new SetFact<Var>();
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me

        //outB-defB
        SetFact<Var> tempout=new SetFact<>();
        tempout.set(out);

        Optional<LValue> l=stmt.getDef();
        if(l.isPresent()){
            LValue lv=l.get();
            if(lv instanceof Var) {
                tempout.remove((Var) lv);
            }
        }

        //outB+useB
        List<RValue> r=stmt.getUses();
        for(RValue Rv:r){
            if(Rv instanceof Var){
                Var v=(Var) Rv;
                tempout.add(v);
            }
        }

        SetFact<Var> oldin=new SetFact<Var>();
        oldin.set(in);
        in.set(tempout);
        return in.equals(oldin);

        //return false;
    }
}
