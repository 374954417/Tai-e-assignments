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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {

        // TODO - finish me
        boolean changed = true;

        Map<Node, Boolean> map= new HashMap<>();
        Stack<Node> stack = new Stack<>();
        for (Node node : cfg.getNodes()) {
            stack.push(node);
            map.put(node, true);
        }

        while(!stack.empty()) {
            Node node = stack.pop();
            map.put(node, false);

            changed = false;
            if(!node.equals(cfg.getEntry())) {
                result.setInFact(node, analysis.newInitialFact());
            }
            for (Node pred : cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pred),result.getInFact(node));
            }

            boolean res = analysis.transferNode(node, result.getInFact(node),result.getOutFact(node));
            changed = changed || res;
            if (changed) {
                for (Node succ : cfg.getSuccsOf(node)) {
                    if(!map.get(succ)) {
                        map.put(succ, true);
                        stack.push(succ);
                    }
                }
            }
        }
    }


    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}

