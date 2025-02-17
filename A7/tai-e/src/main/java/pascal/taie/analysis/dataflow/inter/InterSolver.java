/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.*;
import java.util.stream.Collectors;

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

    DataflowResult<Node, Fact> getResult() {
        return result;
    }

    private void initialize() {
       // TODO - finish me
         /* TODO - finish me */
        for (Node node : icfg) {
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
        // 遍历所有icfg的所有方法，
        for (Method method : icfg.entryMethods().toList()) {
            Node entry = icfg.getEntryOf(method);
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        }
    }

    private void doSolve() {
        /* TODO - finish me */
        Set<Node> workSet = new HashSet<>();
    for (Node node : icfg) {
        workSet.add(node);
    }

    while (!workSet.isEmpty()) {
        Set<Node> nextWorkSet = new HashSet<>();
        for (Node node : workSet)
        {
            Set<ICFGEdge<Node>> inEdges = icfg.getInEdgesOf(node);
            for (ICFGEdge<Node> edge : inEdges)
            {
                Fact sourceOutFact = result.getOutFact(edge.getSource());
                Fact edgeFact = analysis.transferEdge(edge, sourceOutFact);
                analysis.meetInto(edgeFact, result.getInFact(node));
            }
            boolean changed = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if (changed)
            {
                nextWorkSet.addAll(icfg.getSuccsOf(node));
            }
        }
        workSet = nextWorkSet;
        }
    }


    public void addWorkList(Node node){
        if(!workList.contains(node)){
            workList.add(node);
        }
    }
}