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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.getClassHierarchy();
        // initialize main method
        JMethod main = World.getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(!callGraph.contains(method)){
            callGraph.addReachableMethod(method);
            List<Stmt> mStmt= method.getIR().getStmts();
            for(Stmt stmt:mStmt){
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            Var lVar=stmt.getLValue();
            Obj obj=heapModel.getObj(stmt);
            VarPtr varPtr=pointerFlowGraph.getVarPtr(lVar);
            PointsToSet pointsToSet=new PointsToSet(obj);
            workList.addEntry(varPtr,pointsToSet);
            return null;
        }
        public Void visit(Copy stmt){
            Var lVar=stmt.getLValue();
            Var rVar=stmt.getRValue();
            VarPtr lVarPtr=pointerFlowGraph.getVarPtr(lVar);
            VarPtr rVarPtr=pointerFlowGraph.getVarPtr(rVar);
            addPFGEdge(rVarPtr,lVarPtr);
            return null;
        }
        public Void  visit(LoadField stmt) {
            if(stmt.isStatic()){
                Var lVar=stmt.getLValue();
                VarPtr lVarPtr=pointerFlowGraph.getVarPtr(lVar);
                JField field =stmt.getFieldRef().resolve();
                StaticField staticField=pointerFlowGraph.getStaticField(field);
                addPFGEdge(staticField,lVarPtr);
            }
            return null;
        }
        public Void  visit(StoreField stmt) {
            if(stmt.isStatic()){
                Var rVar=stmt.getRValue();
                VarPtr rVarPtr=pointerFlowGraph.getVarPtr(rVar);
                JField field =stmt.getFieldRef().resolve();
                StaticField staticField=pointerFlowGraph.getStaticField(field);
                addPFGEdge(rVarPtr,staticField);
            }
            return null;
        }
        public Void  visit(Invoke stmt){
            if(stmt.isStatic()){
                JMethod jMethod=resolveCallee(null,stmt);
                if(callGraph.addEdge(new Edge<Invoke,JMethod>(CallKind.STATIC,stmt,jMethod))){
                    addReachable(jMethod);
                    Var lVar=stmt.getResult();
                    if(lVar!=null){
                        VarPtr lVarPtr=pointerFlowGraph.getVarPtr(lVar);
                        List<Var>rReturnVars=jMethod.getIR().getReturnVars();
                        for(Var var:rReturnVars){
                            VarPtr varPtr=pointerFlowGraph.getVarPtr(var);
                            addPFGEdge(varPtr,lVarPtr);
                        }
                    }

                    InvokeExp invokeExp=stmt.getRValue();
                    List<Var>rListArgs=invokeExp.getArgs();
                    List<Var>rListParams=jMethod.getIR().getParams();

                    for(int i=0;i<rListArgs.size();i++){
                        VarPtr argPtr=pointerFlowGraph.getVarPtr(rListArgs.get(i));
                        VarPtr paramPtr=pointerFlowGraph.getVarPtr(rListParams.get(i));
                        addPFGEdge(argPtr,paramPtr);
                    }
                }

            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source,target)){
           if(!source.getPointsToSet().isEmpty()){
               workList.addEntry(target,source.getPointsToSet());
           }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            PointsToSet diffPointToSet=new PointsToSet();
            WorkList.Entry entry=workList.pollEntry();
            diffPointToSet=propagate(entry.pointer,entry.pointsToSet);
            if(entry.pointer instanceof  VarPtr){
                VarPtr varPtr=(VarPtr) entry.pointer;
                Var var=varPtr.getVar();
               if(diffPointToSet!=null&&!diffPointToSet.isEmpty()){
                   for(Obj obj:diffPointToSet){
                       List<StoreField>storeFields=var.getStoreFields();
                       for(StoreField storeField:storeFields){
                           Var rVar=storeField.getRValue();
                           VarPtr rVarPtr=pointerFlowGraph.getVarPtr(rVar);
                           JField field=storeField.getFieldRef().resolve();
                           InstanceField instanceField=pointerFlowGraph.getInstanceField(obj,field);
                           addPFGEdge(rVarPtr,instanceField);

                       }
                       List<LoadField>loadFields=var.getLoadFields();
                       for(LoadField loadField:loadFields){
                           Var lVar=loadField.getLValue();
                           VarPtr lVarPtr=pointerFlowGraph.getVarPtr(lVar);
                           JField field=loadField.getFieldRef().resolve();
                           InstanceField instanceField=pointerFlowGraph.getInstanceField(obj,field);
                           addPFGEdge(instanceField,lVarPtr);
                       }
                       List<StoreArray>storeArrays=var.getStoreArrays();
                       for(StoreArray storeArray:storeArrays){
                           Var rVar=storeArray.getRValue();
                           VarPtr rVarPtr=pointerFlowGraph.getVarPtr(rVar);
                           ArrayIndex arrayIndex=pointerFlowGraph.getArrayIndex(obj);
                           addPFGEdge(rVarPtr,arrayIndex);
                       }
                       List<LoadArray>loadArrays=var.getLoadArrays();
                       for(LoadArray loadArray:loadArrays){
                           Var lVar=loadArray.getLValue();
                           VarPtr lVarPtr=pointerFlowGraph.getVarPtr(lVar);
                           ArrayIndex arrayIndex=pointerFlowGraph.getArrayIndex(obj);
                           addPFGEdge(arrayIndex,lVarPtr);
                       }
                       processCall(var,obj);
                   }
               }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        if(pointsToSet.isEmpty()){
            return null;
        }
        PointsToSet diffPointsToSet=new PointsToSet();
        for(Obj obj:pointsToSet){
            if(pointer.getPointsToSet().addObject(obj)){
                diffPointsToSet.addObject(obj);
            }
        }
        pointerFlowGraph.succsOf(pointer).forEach(succ->{
            workList.addEntry(succ,diffPointsToSet);
        });
        return diffPointsToSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        List<Invoke>invokes=var.getInvokes();
        for(Invoke invoke:invokes){
            JMethod method=resolveCallee(recv,invoke);
            Var thisVar=method.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(thisVar),new PointsToSet(recv));
            boolean change = false;
            if(invoke.isInterface()){
                change=callGraph.addEdge(new Edge<Invoke,JMethod>(CallKind.INTERFACE,invoke,method));
            }else if(invoke.isVirtual()){
                change=callGraph.addEdge(new Edge<Invoke,JMethod>(CallKind.VIRTUAL,invoke,method));
            }else if(invoke.isDynamic()){
                change=callGraph.addEdge(new Edge<Invoke,JMethod>(CallKind.DYNAMIC,invoke,method));
            }else if(invoke.isSpecial()){
                change=callGraph.addEdge(new Edge<Invoke,JMethod>(CallKind.SPECIAL,invoke,method));
            }else{
                change=callGraph.addEdge(new Edge<Invoke,JMethod>(CallKind.OTHER,invoke,method));
            }
            if(change){
               addReachable(method);
                Var lVar=invoke.getLValue();
                JMethod jMethod=resolveCallee(recv,invoke);
                if(lVar!=null){
                    VarPtr lVarPtr=pointerFlowGraph.getVarPtr(lVar);
                    List<Var>rReturnVars=jMethod.getIR().getReturnVars();
                    for(Var returnVar:rReturnVars){
                        VarPtr varPtr=pointerFlowGraph.getVarPtr(returnVar);
                        addPFGEdge(varPtr,lVarPtr);
                    }
                }
                List<Var>rListParams=jMethod.getIR().getParams();
                InvokeExp invokeExp=invoke.getRValue();
                List<Var>rListArgs=invokeExp.getArgs();
                for(int i=0;i<rListArgs.size();i++){
                    VarPtr argPtr=pointerFlowGraph.getVarPtr(rListArgs.get(i));
                    VarPtr paramPtr=pointerFlowGraph.getVarPtr(rListParams.get(i));
                    addPFGEdge(argPtr,paramPtr);
                }
            }

        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
