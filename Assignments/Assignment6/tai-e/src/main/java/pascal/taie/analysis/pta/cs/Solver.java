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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.lang.reflect.Method;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(HeapModel heapModel, ContextSelector contextSelector) {
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        StmtProcessor stmtProcessor=new StmtProcessor(csMethod);
        if(callGraph.addReachableMethod(csMethod)){
            for(Stmt stmt:csMethod.getMethod().getIR().getStmts()){
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }
        public Void visit(New stmt) {
            Context heapContext=contextSelector.selectHeapContext(csMethod,heapModel.getObj(stmt));
            CSVar csVar=csManager.getCSVar(heapContext, stmt.getLValue());
            CSObj csObj=csManager.getCSObj(heapContext,heapModel.getObj(stmt));
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            return null;
        }
        public Void visit(Copy stmt){
            CSVar csVarLeft=csManager.getCSVar(context,stmt.getLValue());
            CSVar csVarRight=csManager.getCSVar(context,stmt.getRValue());
            addPFGEdge(csVarRight,csVarLeft);
            return null;
        }
        public Void  visit(LoadField stmt) {
            if(stmt.isStatic()){
                CSVar csVar=csManager.getCSVar(context,stmt.getLValue());
                StaticField staticField= csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(staticField,csVar);
            }
            return null;
        }
        public Void  visit(StoreField stmt) {
            if(stmt.isStatic()){
                CSVar csVar=csManager.getCSVar(context,stmt.getRValue());
                StaticField staticField=csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(csVar,staticField);
            }
            return null;
        }
        public Void  visit(Invoke stmt) {
            if(stmt.isStatic()){
                JMethod jMethod=resolveCallee(null,stmt);
                CSCallSite csCallSite=csManager.getCSCallSite(context,stmt);
                Context staticContext=contextSelector.selectContext(csCallSite,jMethod);
                CSMethod csMethod=csManager.getCSMethod(staticContext,jMethod);
                if(callGraph.addEdge(new Edge<CSCallSite, CSMethod>(CallKind.STATIC,csCallSite,csMethod))){
                    addReachable(csMethod);

                    for(Var var:jMethod.getIR().getReturnVars()){
                        addPFGEdge(csManager.getCSVar(staticContext,var),csManager.getCSVar(context,stmt.getLValue()));
                    }

                    List<Var>Args=stmt.getRValue().getArgs();
                    List<Var>Params=jMethod.getIR().getParams();
                    for(int i=0;i<Args.size();i++){
                        addPFGEdge(csManager.getCSVar(context,Args.get(i)),csManager.getCSVar(staticContext,Params.get(i)));
                    }
                }
            }
            return null;
        }
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
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
        
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        return null;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
