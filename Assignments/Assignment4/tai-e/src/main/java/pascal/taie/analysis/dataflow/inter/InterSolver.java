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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Stream;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        List<Node>visit=new LinkedList<>();
        Stream<Method> entry=icfg.entryMethods();
        entry.forEach(entryMethod->{
            Node node=icfg.getEntryOf(entryMethod);
            visit.add(node);
            result.setOutFact(node, analysis.newBoundaryFact(node));
        });
        for(Node node:icfg){
            if(!visit.contains(node)){
                result.setOutFact(node, analysis.newInitialFact());
            }
            result.setInFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
        // TODO - finish me
        workList=new LinkedList<>();
        for(Node node:icfg){
            workList.add(node);
        }
        while (!workList.isEmpty()){
            Node node=workList.remove();
            icfg.predsOf(node).forEach(pred->{
                Stream<ICFGEdge<Node>> outEdge=icfg.outEdgesOf(pred);
                outEdge.forEach(out->{
                    if(out.getTarget()==node){
                        Fact fact=analysis.transferEdge(out,result.getOutFact(pred));
                        analysis.meetInto(fact,result.getInFact(node));
                    }
                });
            });
            boolean change=analysis.transferNode(node,result.getInFact(node),result.getOutFact(node));
            if(change){
                icfg.succsOf(node).forEach(workList::add);
            }
        }
    }
}
