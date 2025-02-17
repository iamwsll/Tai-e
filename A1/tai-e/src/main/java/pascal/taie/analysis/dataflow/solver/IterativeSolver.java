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

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        boolean has_changed = true;
        while(has_changed)
        {
            int cnt = 0;
            for(Node node : cfg.getNodes())
            {
                //第一句
                Fact out_B = result.getOutFact(node);
                for(Node successor : cfg.getSuccsOf(node))
                {
                    Fact in_S = result.getInFact(successor);
                    analysis.meetInto(in_S, out_B);
                }
                //第二句
                Fact in_B = result.getInFact(node);
                if(analysis.transferNode(node,in_B,out_B))
                {
                    cnt++;
                }
                //更新in和out
                result.setInFact(node, in_B);
                result.setOutFact(node, out_B);
            }
            //如果没有节点的in改变了，就结束
            if(cnt == 0)
            {
                has_changed = false;
            }
        }
    }
}
