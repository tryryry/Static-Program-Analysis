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

import pascal.taie.analysis.IntraproceduralAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class DeadCodeDetection extends IntraproceduralAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me

        //1.get all stmt
        List<Stmt> allStmt=ir.getStmts();
        allStmt=new ArrayList<>(allStmt);

        //2.traverse cfg
        Stmt entry=cfg.getEntry();
        Stream<Edge<Stmt>> next=cfg.outEdgesOf(entry);
        Queue<Edge<Stmt>> queue=next.collect(Collectors.toCollection(LinkedList::new));
        List<Edge<Stmt>> visit=new ArrayList<>();
        while(!queue.isEmpty()){
            Edge<Stmt> top=queue.remove();
            visit.add(top);
            Stmt reachStmt=top.getTarget();
            //2.1 remove reach stmt from all stmt
            allStmt.remove(reachStmt);

            if(reachStmt instanceof If){
                //2.2 analysis if
                If ifStmt=(If)reachStmt;
                ConditionExp conExp=ifStmt.getCondition();
                Var var1=conExp.getOperand1();
                Var var2=conExp.getOperand2();
                CPFact cpFact=constants.getInFact(ifStmt);
                if(cpFact.get(var1).isConstant()&&cpFact.get(var2).isConstant()){
                    Value value=ConstantPropagation.evaluate(conExp,cpFact);
                    Stream<Edge<Stmt>> reachNext=cfg.outEdgesOf(reachStmt);
                    if(value.getConstant()==1){
                        reachNext.forEach(edge->{
                            if(edge.getKind()== Edge.Kind.IF_TRUE){
                                if(!visit.contains(edge))
                                    queue.add(edge);
                            }
                        });
                    }else{
                        reachNext.forEach(edge->{
                            if(edge.getKind()== Edge.Kind.IF_FALSE){
                                if(!visit.contains(edge))
                                    queue.add(edge);
                            }
                        });
                    }
                }else{
                    Stream<Edge<Stmt>> reachNext=cfg.outEdgesOf(reachStmt);
                    reachNext.forEach(edge->{
                        if(!visit.contains(edge))
                            queue.add(edge);
                    });
                }

            }else if(reachStmt instanceof SwitchStmt){
                //2.2 analysis Switch
                SwitchStmt switchStmt=(SwitchStmt) reachStmt;
                Var var=switchStmt.getVar();
                CPFact cpFact=constants.getInFact(switchStmt);
                if(cpFact.get(var).isConstant()){
                    int constInt=cpFact.get(var).getConstant();
                    Stream<Edge<Stmt>> reachNext=cfg.outEdgesOf(reachStmt);
                    reachNext.forEach(edge->{
                        if(edge.getKind()== Edge.Kind.SWITCH_CASE){
                            int caseValue=edge.getCaseValue();
                            if(caseValue==constInt)
                                if(!visit.contains(edge))
                                    queue.add(edge);
                        }
                    });
                }else{
                    Stream<Edge<Stmt>> reachNext=cfg.outEdgesOf(reachStmt);
                    reachNext.forEach(edge->{
                        if(!visit.contains(edge))
                            queue.add(edge);
                    });
                }

            }else if(reachStmt instanceof AssignStmt){
                //2.3 analysis assign
                AssignStmt assignStmt=(AssignStmt)reachStmt;
                Exp exp=assignStmt.getLValue();
                Var var=null;
                if(exp instanceof Var){
                    var=(Var)exp;
                }
                SetFact setFact=liveVars.getOutFact(reachStmt);
                if(!setFact.contains(var)){
                    if(hasNoSideEffect(assignStmt.getRValue())){
                        allStmt.add(assignStmt);
                    }
                }
                Stream<Edge<Stmt>> reachNext=cfg.outEdgesOf(reachStmt);
                reachNext.forEach(edge->{
                    if(!visit.contains(edge))
                        queue.add(edge);
                });
            }else{
                Stream<Edge<Stmt>> reachNext=cfg.outEdgesOf(reachStmt);
                reachNext.forEach(edge->{
                    if(!visit.contains(edge))
                        queue.add(edge);
                });
            }
        }

        //3.add deadCode
        deadCode.addAll(allStmt);


        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
