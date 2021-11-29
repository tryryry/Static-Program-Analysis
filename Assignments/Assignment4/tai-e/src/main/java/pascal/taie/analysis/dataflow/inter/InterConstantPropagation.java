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

 package pascal.taie.analysis.dataflow.inter;

 import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
 import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
 import pascal.taie.analysis.dataflow.analysis.constprop.Value;
 import pascal.taie.analysis.graph.cfg.CFGBuilder;
 import pascal.taie.analysis.graph.icfg.CallEdge;
 import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
 import pascal.taie.analysis.graph.icfg.NormalEdge;
 import pascal.taie.analysis.graph.icfg.ReturnEdge;
 import pascal.taie.config.AnalysisConfig;
 import pascal.taie.ir.IR;
 import pascal.taie.ir.exp.Exp;
 import pascal.taie.ir.exp.InvokeExp;
 import pascal.taie.ir.exp.Var;
 import pascal.taie.ir.stmt.DefinitionStmt;
 import pascal.taie.ir.stmt.Stmt;
 import pascal.taie.language.classes.JMethod;

 import java.util.List;
 import java.util.concurrent.atomic.AtomicReference;
 import java.util.stream.Collectors;
 import java.util.stream.Stream;

 /**
  * Implementation of interprocedural constant propagation for int values.
  */
 public class InterConstantPropagation extends
         AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

     public static final String ID = "inter-constprop";

     private final ConstantPropagation cp;

     public InterConstantPropagation(AnalysisConfig config) {
         super(config);
         cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
     }

     @Override
     public boolean isForward() {
         return cp.isForward();
     }

     @Override
     public CPFact newBoundaryFact(Stmt boundary) {
         IR ir = icfg.getContainingMethodOf(boundary).getIR();
         return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
     }

     @Override
     public CPFact newInitialFact() {
         return cp.newInitialFact();
     }

     @Override
     public void meetInto(CPFact fact, CPFact target) {
         cp.meetInto(fact, target);
     }

     @Override
     protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
         // TODO - finish me
        //return false;
        return out.copyFrom(in);
     }

     @Override
     protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
         // TODO - finish me
         //return false;
         return cp.transferNode(stmt,in,out);
     }

     @Override
     protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
         // TODO - finish me
         //return null;
         CPFact temp=new CPFact();
         temp.copyFrom(out);
         return temp;
     }

     @Override
     protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
         // TODO - finish me
        // return null;
         CPFact temp=new CPFact();
         temp.copyFrom(out);
         Stmt stmt=edge.getSource();
         if(stmt instanceof DefinitionStmt){
             DefinitionStmt definitionStmt=(DefinitionStmt) stmt;
             Exp exp=definitionStmt.getLValue();
             if(exp instanceof Var){
                 Var var=(Var)exp;
                 temp.remove(var);
             }
         }
         return temp;
     }

     @Override
     protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
         // TODO - finish me
         //return null;
         CPFact temp=new CPFact();
         Stmt srcStmt=edge.getSource();
         //Stmt dstStmt=edge.getTarget();
         JMethod jMethod=edge.getCallee();
         IR ir=jMethod.getIR();
         List<Var> param=ir.getParams();
         InvokeExp invokeExp = null;
         if(srcStmt instanceof  DefinitionStmt){
             DefinitionStmt definitionStmt=(DefinitionStmt) srcStmt;
             Exp exp=definitionStmt.getRValue();
             if(exp instanceof InvokeExp){
                 invokeExp=(InvokeExp) exp;
             }
         }else{
             Exp exp=(Exp)srcStmt;
             if(exp instanceof InvokeExp)
                 invokeExp=(InvokeExp) exp;
         }
         List<Var>args=invokeExp.getArgs();
         for(int i=0;i<param.size();i++){
             Value value=callSiteOut.get(args.get(i));
             temp.update(param.get(i),value);
         }
         return temp;
     }

     @Override
     protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
         // TODO - finish me
         //return null;
         CPFact temp=new CPFact();
         Stmt stmt=edge.getCallSite();
         if(stmt instanceof DefinitionStmt){
             DefinitionStmt definitionStmt=(DefinitionStmt) stmt;
             Exp exp=definitionStmt.getLValue();
             if(exp instanceof Var){
                 Var var=(Var)exp;
                 Stream<Var> returnVars=edge.returnVars();
                 List<Var> returnVarList=returnVars.collect(Collectors.toList());
                 Value value=null;
                 for(int i=0;i<returnVarList.size();i++){
                     if(returnOut.get(returnVarList.get(i)).isNAC()){
                         value=Value.getNAC();
                         break;
                     }else if(returnOut.get(returnVarList.get(i)).isUndef()){
                         value=Value.getUndef();
                     }else if(returnOut.get(returnVarList.get(i)).isConstant()){
                         if(value==null){
                             value=returnOut.get(returnVarList.get(i));
                         }else if(value.isConstant()){
                             if(value.getConstant()==returnOut.get(returnVarList.get(i)).getConstant()){

                             }else{
                                 value=Value.getNAC();
                             }
                         }else{
                             value=Value.getNAC();
                         }
                     }
                 }
                 temp.update(var,value);
             }
         }
         return temp;
     }
 }
