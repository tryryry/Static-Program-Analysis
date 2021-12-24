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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private class sinkFlow{
        CSVar csVar;
        Invoke stmt;
        int index;
        public sinkFlow(CSVar csVar,Invoke stmt,int index){
            this.csVar=csVar;
            this.stmt=stmt;
            this.index=index;
        }

    }
    private LinkedList<sinkFlow> sinkCSVar;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.getClassHierarchy(),
                World.getTypeManager());
        logger.info(config);
        sinkCSVar=new LinkedList();
    }


    // TODO - finish me
    public boolean isTaintObj(Obj obj){
        return manager.isTaint(obj);
    }
    public void handle(Invoke stmt,Context context){
        //source
        JMethod method=stmt.getInvokeExp().getMethodRef().resolve();
        Type type=stmt.getInvokeExp().getType();

        if(config.getSources().contains(new Source(method,type))){
              CSVar csVar= csManager.getCSVar(context,stmt.getLValue());
              Obj obj=manager.makeTaint(stmt,type);
              CSObj csObj=csManager.getCSObj(emptyContext,obj);
              solver.TaintSolver(csVar,csObj);
        }

        //sink
        int argCount=stmt.getInvokeExp().getArgCount();
        for(int i=0;i<argCount;i++){
            Sink sink=new Sink(method,i);
            if(config.getSinks().contains(sink)){
                CSVar arg=csManager.getCSVar(context,stmt.getInvokeExp().getArg(i));
                sinkCSVar.add(new sinkFlow(arg,stmt,i));
            }
        }

        //transfer
        //arg-to-result
        for(int i=0;i<argCount;i++){
            if(config.getTransfers().contains(new TaintTransfer(method,i,-2,type))){
                CSVar arg=csManager.getCSVar(context,stmt.getInvokeExp().getArg(i));
                solver.TaintAddPFG(arg,csManager.getCSVar(context,stmt.getLValue()));
            }
        }

        if(stmt.isStatic()){
            return;
        }

        //arg-to-base

        InvokeInstanceExp invokeInstanceExp=(InvokeInstanceExp) stmt.getInvokeExp();
        CSVar base=csManager.getCSVar(context,invokeInstanceExp.getBase());
        for(int i=0;i<argCount;i++){
            if(config.getTransfers().contains(new TaintTransfer(method,i,-1,type))){
                CSVar arg=csManager.getCSVar(context,stmt.getInvokeExp().getArg(i));
                solver.TaintAddPFG(arg,base);

            }
        }

        //base-to-result

        if(config.getTransfers().contains(new TaintTransfer(method,-1,-2,type))){
            solver.TaintAddPFG(base,csManager.getCSVar(context,stmt.getLValue()));
        }

    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        for(sinkFlow flow:sinkCSVar){
            System.out.println(flow.stmt.toString());
            for(CSObj csObj:result.getPointsToSet(flow.csVar)){
                if(manager.isTaint(csObj.getObject())){
                    taintFlows.add(new TaintFlow(manager.getSourceCall(csObj.getObject()),flow.stmt,flow.index));
                }
            }
        }

        return taintFlows;
    }
}
