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

     private PointerAnalysisResult pta;

     private Map<FieldRef,Value> staticMap;
     private Set<Stmt>loadStaticStmt;

     private static class Instance{
         private final FieldRef fieldRef;
         private final Var base;

         private static Set<Instance> set=new HashSet<>();

         private Instance(FieldRef fieldRef,Var base){
             this.base=base;
             this.fieldRef=fieldRef;
         }
         public FieldRef getFieldRef(){
             return fieldRef;
         }
         public Var getBase(){
             return base;
         }
         public static Instance Create(FieldRef fieldRef,Var base){
             for(Instance instance:set){
                 if(instance.fieldRef==fieldRef&&instance.base== base){
                     return instance;
                 }
             }
             Instance instance=new Instance(fieldRef,base);
             set.add(instance);
             return instance;
         }
     }
     private Set<Instance>instanceSet;
     private Map<Instance,Value> instanceMap;
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
     private boolean isIndexAli(Value value1,Value value2){
        if(value1.isNAC()&&!value2.isUndef()){
            return true;
        }
        if(value2.isNAC()&&!value1.isUndef()){
            return true;
        }
        if(value1.isConstant()&&value2.isConstant()&&value1.getConstant()==value2.getConstant()){
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
                     return out.copyFrom(temp);
                 }else{
                     Set<Stmt>tempSet=new HashSet<>();
                     tempSet.add(stmt);
                     solver.addNode(tempSet);
                     return false;
                 }
             }else{
                 loadInstanceStmt.add(stmt);
                 InstanceFieldAccess instanceFieldAccess=(InstanceFieldAccess) loadField.getRValue();
                 for(Instance instance:instanceSet){
                    if(isOverLap(instanceFieldAccess.getBase(),instance.getBase())){
                        Value value=instanceMap.get(instance);
                        CPFact temp=in.copy();
                        if(ConstantPropagation.canHoldInt(loadField.getLValue())){
                            temp.update(loadField.getLValue(),value);
                        }
                        return out.copyFrom(temp);
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
                 FieldRef fieldRef=storeField.getLValue().getFieldRef();
                 if(staticMap.containsKey(fieldRef)){
                     Value value1=staticMap.get(fieldRef);
                     Value meetValue=cp.meetValue(value1,value);
                     staticMap.replace(fieldRef,meetValue);
                 }else{
                     staticMap.put(fieldRef,value);
                 }
                 boolean isChange=false;
                 for(Map.Entry<FieldRef,Value> entry:staticMap.entrySet()){
                     if(tempMap.get(entry.getKey())!=entry.getValue()){
                         isChange=true;
                         break;
                     }
                 }
                 if(isChange){
                     solver.addNode(loadStaticStmt);
                 }

             }else{
                 Map<Instance,Value>tempMap=new HashMap<>();
                 for(Map.Entry<Instance,Value> entry:instanceMap.entrySet()){
                     tempMap.put(entry.getKey(),entry.getValue());
                 }
                 InstanceFieldAccess instanceFieldAccess=(InstanceFieldAccess) storeField.getLValue();
                 Instance instance=Instance.Create(instanceFieldAccess.getFieldRef(),instanceFieldAccess.getBase());
                 for(Instance instance1:instanceSet) {
                     if(isOverLap(instance.getBase(),instance1.getBase())) {
                         Value value1=instanceMap.get(instance1);
                         Value meetValue=cp.meetValue(value1,value);
                         instanceMap.replace(instance1,meetValue);
                         value=meetValue;
                     }
                 }
                 instanceSet.add(instance);
                 instanceMap.put(instance,value);
                 boolean isChange=false;
                 for(Map.Entry<Instance,Value> entry:instanceMap.entrySet()){
                     if(tempMap.get(entry.getKey())!=entry.getValue()){
                         isChange=true;
                         break;
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
             for(Array array:arraySet){
                 if(isOverLap(array.getBase(),arrayAccess.getBase())&&isIndexAli(ConstantPropagation.evaluate(arrayAccess.getIndex(),in),array.getValue())){
                     if(array.getValue().isNAC()){
                         if(flag){
                             continue;
                         }
                     }
                     CPFact temp=in.copy();
                     Value value=arrayMap.get(array);
                     if(ConstantPropagation.canHoldInt(loadArray.getLValue())){
                         temp.update(loadArray.getLValue(),value);
                     }
                     flag=true;
                     ret=out.copyFrom(temp);
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
             Value indexValue=ConstantPropagation.evaluate(arrayAccess.getIndex(),in);
             Array array=Array.Create(arrayAccess.getBase(),indexValue);
             for(Array array1:arraySet){
                 if(isOverLap(array.getBase(),array1.getBase())&&isIndexAli(array.getValue(),array1.getValue())){
                     Value value1=arrayMap.get(array1);
                     Value meetValue=cp.meetValue(value1,value);
                     if(!array1.getValue().isNAC()){
                         arrayMap.replace(array1,meetValue);
                     }
                     if(!array.getValue().isNAC()){
                         value=meetValue;
                     }
                 }
             }
             arraySet.add(array);
             arrayMap.put(array,value);

             boolean isChange=false;
             for(Map.Entry<Array,Value> entry:arrayMap.entrySet()){
                 if(tempMap.get(entry.getKey())!=entry.getValue()){
                     isChange=true;
                     break;
                 }
             }
             if(isChange){
                 solver.addNode(loadArrayStmt);
             }
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
