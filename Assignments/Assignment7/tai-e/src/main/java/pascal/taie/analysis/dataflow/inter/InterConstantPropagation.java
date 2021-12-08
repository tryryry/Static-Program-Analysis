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

 import pascal.taie.World;
 import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
 import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
 import pascal.taie.analysis.dataflow.analysis.constprop.Value;
 import pascal.taie.analysis.graph.cfg.CFGBuilder;
 import pascal.taie.analysis.graph.icfg.CallEdge;
 import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
 import pascal.taie.analysis.graph.icfg.NormalEdge;
 import pascal.taie.analysis.graph.icfg.ReturnEdge;
 import pascal.taie.analysis.pta.PointerAnalysisResult;
 import pascal.taie.analysis.pta.core.heap.Obj;
 import pascal.taie.config.AnalysisConfig;
 import pascal.taie.ir.IR;
 import pascal.taie.ir.exp.*;
 import pascal.taie.ir.proginfo.FieldRef;
 import pascal.taie.ir.stmt.*;
 import pascal.taie.language.classes.JMethod;

 import java.util.*;
 import java.util.List;
 import java.util.stream.Collectors;
 import java.util.stream.Stream;

 /**
  * Implementation of interprocedural constant propagation for int values.
  */
 public class InterConstantPropagation extends
         AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

     public static final String ID = "inter-constprop";

     private final ConstantPropagation cp;


     private Map<FieldRef,Value> staticMap;
     private Set<Stmt>loadStaticStmt;

     private PointerAnalysisResult pta;

     private Set<InstanceFieldAccess>instanceSet;
     private Map<String,Value> instanceMap;
     private Set<Stmt>loadInstanceStmt;

     private static class Array{
         private final Var base;

         private final Value value;

         public static Set<Array>set=new HashSet<>();
         private Array(Var base, Value value) {
             this.base = base;
             this.value = value;
         }
         Var getBase(){
             return base;
         }
         Value getValue(){
             return value;
         }
         public static Array Create(Var base, Value value){
             for(Array array:set){
                 if(array.base==base&&array.value==value)
                     return array;
             }
             Array newArray=new Array(base,value);
             set.add(newArray);
             return newArray;
         }
     }
     private Set<Array>arraySet;
     private Map<Array,Value> arrayMap;
     private Set<Stmt>loadArrayStmt;
     public InterConstantPropagation(AnalysisConfig config) {
         super(config);
         cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
     }

     @Override
     protected void initialize() {
         String ptaId = getOptions().getString("pta");
         PointerAnalysisResult pta = World.getResult(ptaId);
         // You can do initialization work here
         this.pta=pta;
         staticMap=new HashMap<>();
         loadStaticStmt=new HashSet<>();

         instanceSet=new HashSet<>();
         instanceMap=new HashMap<>();
         loadInstanceStmt=new HashSet<>();

         arraySet=new HashSet<>();
         arrayMap=new HashMap<>();
         loadArrayStmt=new HashSet<>();
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

         return out.copyFrom(in);
     }
     private boolean isOverLap(Var var1,Var var2){
         Set<Obj>set1=pta.getPointsToSet(var1);
         Set<Obj>set2=pta.getPointsToSet(var2);
         for(Obj obj:set1){
             if(set2.contains(obj)){
                 return true;
             }
         }
         return false;
     }
     private boolean isEqual(Value v1,Value v2){
         if(v1.isConstant()&&v2.isConstant()&&v1.getConstant()==v2.getConstant()){
             return true;
         }else if(v1.isNAC()&&v2.isNAC()){
             return true;
         }else if(v1.isUndef()||v2.isUndef()){
             return true;
         }
         return false;
     }
     private boolean isAli(Var var1,CPFact in1,Value value2){
        Value value1=ConstantPropagation.evaluate(var1,in1);

        if(value1.isNAC()&&!value2.isUndef()){
            return true;
        }
        if(value2.isNAC()&&!value1.isUndef()){
            return true;
        }
        if(value1.isConstant()&&value2.isConstant()){
            if(value1.getConstant()==value2.getConstant())
                return true;
        }
        return false;
     }
     @Override
     protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
         // TODO - finish me
         //return false;
         if(stmt instanceof LoadField){

             LoadField loadField=(LoadField) stmt;
             if(loadField.isStatic()){
                 loadStaticStmt.add(stmt);
                 if(staticMap.containsKey(loadField.getRValue().getFieldRef())){
                     CPFact temp=in.copy();
                     Value value=staticMap.get(loadField.getRValue().getFieldRef());
                     if(ConstantPropagation.canHoldInt(loadField.getLValue())){
                         temp.update(loadField.getLValue(),value);
                     }
                     boolean flag=out.copyFrom(temp);
                     return flag;
                 }else{
                     Set<Stmt>tempSet=new HashSet<>();
                     tempSet.add(stmt);
                     solver.addNode(tempSet);
                     return false;
                 }
             }else{
                 loadInstanceStmt.add(stmt);
                InstanceFieldAccess instanceFieldAccess=(InstanceFieldAccess) loadField.getRValue();
                for(InstanceFieldAccess instanceFieldAccess1:instanceSet){
                    if(isOverLap(instanceFieldAccess.getBase(),instanceFieldAccess1.getBase())){
                        //String str=instanceFieldAccess.getBase().toString()+"."+instanceFieldAccess.getFieldRef().toString();
                        String str1=instanceFieldAccess1.getBase().toString()+"."+instanceFieldAccess.getFieldRef().toString();
                        CPFact temp=in.copy();
                        Value value=instanceMap.get(str1);
                        //instanceMap.put(str,value);
                        if(ConstantPropagation.canHoldInt(loadField.getLValue())){
                            temp.update(loadField.getLValue(),value);
                        }
                        boolean flag=out.copyFrom(temp);
                        return flag;
                    }
                }
                 Set<Stmt>tempSet=new HashSet<>();
                 tempSet.add(stmt);
                 solver.addNode(tempSet);
                 return false;
             }
         }else if(stmt instanceof StoreField){
             StoreField storeField=(StoreField) stmt;
             Value value=ConstantPropagation.evaluate(storeField.getRValue(),in);
             if(storeField.isStatic()){
                 Map<FieldRef,Value>tempMap=new HashMap<>();
                 for(Map.Entry<FieldRef,Value> entry:staticMap.entrySet()){
                     tempMap.put(entry.getKey(),entry.getValue());
                 }
                 if(staticMap.containsKey(storeField.getLValue().getFieldRef())){
                     if(!isEqual(staticMap.get(storeField.getLValue().getFieldRef()),value)){
                         staticMap.replace(storeField.getLValue().getFieldRef(),Value.getNAC());
                     }
                 }else{
                        staticMap.put(storeField.getLValue().getFieldRef(),value);
                 }
                 boolean isChange=false;
                 for(Map.Entry<FieldRef,Value> entry:staticMap.entrySet()){
                     if(tempMap.get(entry.getKey())!=entry.getValue()){
                         isChange=true;
                     }
                 }
                 if(isChange){
                     solver.addNode(loadStaticStmt);
                 }

             }else{
                 Map<String,Value>tempMap=new HashMap<>();
                 for(Map.Entry<String,Value> entry:instanceMap.entrySet()){
                     tempMap.put(entry.getKey(),entry.getValue());
                 }
                 InstanceFieldAccess instanceFieldAccess=(InstanceFieldAccess) storeField.getLValue();
                 String str=instanceFieldAccess.getBase().toString()+"."+instanceFieldAccess.getFieldRef().toString();
                 for(InstanceFieldAccess instanceFieldAccess1:instanceSet) {
                     if(isOverLap(instanceFieldAccess.getBase(),instanceFieldAccess1.getBase())) {
                         String str1=instanceFieldAccess1.getBase().toString()+"."+instanceFieldAccess.getFieldRef().toString();
                         Value value1=instanceMap.get(str1);
                         if(!isEqual(value1,value)){
                             value=Value.getNAC();
                             instanceMap.replace(str1,value);
                         }else if(value1.isUndef()&&value.isConstant()){
                             instanceMap.replace(str1,value);
                         }else if(value1.isConstant()&&value.isUndef()){
                             value=value1;
                         }
                     }
                 }
                 instanceMap.put(str,value);
                 instanceSet.add(instanceFieldAccess);
                 boolean isChange=false;
                 for(Map.Entry<String,Value> entry:instanceMap.entrySet()){
                     if(tempMap.get(entry.getKey())!=entry.getValue()){
                         isChange=true;
                     }
                 }
                 if(isChange){
                     solver.addNode(loadInstanceStmt);
                 }

             }
         }
         else if(stmt instanceof LoadArray){
             loadArrayStmt.add(stmt);
             LoadArray loadArray=(LoadArray)stmt;
             ArrayAccess arrayAccess=loadArray.getRValue();
             boolean flag=false;
             boolean ret=false;
             int num=0;
             for(Array array:arraySet){
                 if(isOverLap(array.getBase(),arrayAccess.getBase())&&isAli(arrayAccess.getIndex(),in,array.getValue())){
                     Array key1=Array.Create(array.getBase(),array.getValue());
                     if(key1.getValue().isNAC()){
                         if(num!=0){
                             continue;
                         }
                     }
                     CPFact temp=in.copy();
                     Value value=arrayMap.get(key1);
                     if(ConstantPropagation.canHoldInt(loadArray.getLValue())){
                         temp.update(loadArray.getLValue(),value);
                     }
                     flag=true;
                     ret=out.copyFrom(temp);
                     num++;
                 }
             }
             if(flag){
                 return ret;
             }
             Set<Stmt>tempSet=new HashSet<>();
             tempSet.add(stmt);
             solver.addNode(tempSet);
             return false;
         }else if(stmt instanceof StoreArray){
             Map<Array,Value>tempMap=new HashMap<>();
             for(Map.Entry<Array,Value> entry:arrayMap.entrySet()){
                 tempMap.put(entry.getKey(),entry.getValue());
             }

             StoreArray storeArray=(StoreArray) stmt;
             Value value=ConstantPropagation.evaluate(storeArray.getRValue(),in);
             ArrayAccess arrayAccess=storeArray.getArrayAccess();
             Array key=Array.Create(arrayAccess.getBase(),ConstantPropagation.evaluate(arrayAccess.getIndex(),in));
             for(Array array:arraySet){
                 if(isOverLap(key.getBase(),array.getBase())&&isAli(arrayAccess.getIndex(),in,array.getValue())){
                     Array key1=Array.Create(array.getBase(),array.getValue());
                     Value value1=arrayMap.get(key1);

                     if(!isEqual(value1,value)) {
                         if(array.getValue()!=Value.getNAC()){
                             arrayMap.replace(key1, Value.getNAC());
                         }
                         if(key.getValue()!=Value.getNAC()){
                             value=Value.getNAC();
                         }

                     }
                 }
             }

             arrayMap.put(key,value);
             arraySet.add(key);

             boolean isChange=false;
             for(Map.Entry<Array,Value> entry:arrayMap.entrySet()){
                 if(tempMap.get(entry.getKey())!=entry.getValue()){
                     isChange=true;
                 }
             }
             if(isChange){
                 solver.addNode(loadArrayStmt);
             }
             //solver.addNode(loadArrayStmt);
         }
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
         //return null;
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
