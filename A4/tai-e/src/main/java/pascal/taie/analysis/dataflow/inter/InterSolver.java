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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.*;
import java.util.stream.Collectors;
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
        Stream<Method> entris = icfg.entryMethods();
        Set<Method> entrySet = entris.collect(Collectors.toSet());
        Set<Node> entrynodes = new HashSet<>();
        for (Method m : entrySet) {
            entrynodes.add(icfg.getEntryOf(m));
        }

        if(entrynodes.size() > 1) {throw new UnsupportedOperationException("more than one entry method!");}

        for (Node node : icfg) {
            if (entrynodes.contains(node)) {
                result.setInFact(node, analysis.newBoundaryFact(node));
            } else {
                result.setInFact(node, analysis.newInitialFact()); // 若是引用类型，记得 copy！
            }
            result.setOutFact(node, analysis.newInitialFact());
        }

    }

    private void doSolve() {
        // TODO - finish me

        Stream<Method> entris = icfg.entryMethods();
        Set<Method> entrySet = entris.collect(Collectors.toSet());
        Set<Node> entrynodes = new HashSet<>();
        for (Method m : entrySet) {
            entrynodes.add(icfg.getEntryOf(m));
        }

        boolean changed = true;

        Map<Node, Boolean> map= new HashMap<>();
        Stack<Node> stack = new Stack<>();
        for (Node node : icfg) {
            stack.push(node);
            map.put(node, true);
        }

        while(!stack.empty()) {
            Node node = stack.pop();
            System.out.println("node: " + node);
            map.put(node, false);

            changed = false;
            if(!entrynodes.contains(node)) {
                result.setInFact(node, analysis.newInitialFact());
            }

            for(ICFGEdge<Node> edge: icfg.getInEdgesOf(node)){
                Fact processed = analysis.transferEdge(edge,result.getOutFact(edge.getSource()));
                analysis.meetInto(processed,result.getInFact(node));
            }

//            analysis.meetInto(result.getInFact(node), result.getOutFact(node) );
            boolean res = analysis.transferNode(node, result.getInFact(node),result.getOutFact(node));
            changed = changed || res;
            if (changed) {
                for (Node succ : icfg.getSuccsOf(node)) {
                    if(!map.get(succ)) {
                        map.put(succ, true);
                        stack.push(succ);
                    }
                }
            }
        }
    }

}
