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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

    Set<Stmt> liveCode = new HashSet<>();
    Queue<Stmt> worklist = new LinkedList<>();

    worklist.add(cfg.getEntry());
    worklist.add(cfg.getExit());
    while (!worklist.isEmpty())
    {
        Stmt stmt = worklist.poll();

        if (!liveCode.add(stmt))
        {
            continue;
        }

        if (stmt instanceof AssignStmt<?, ?> assignStmt)
        {
            LValue lValue = assignStmt.getLValue();
            RValue rValue = assignStmt.getRValue();
            SetFact<Var> liveOut = liveVars.getOutFact(stmt);

            if (lValue instanceof Var var && !liveOut.contains(var) && hasNoSideEffect(rValue)) {
                //liveCode.remove(stmt);
                deadCode.add(stmt);
            }

            for (Stmt succ : cfg.getSuccsOf(stmt))
            {
                if (succ != null)
                {
                    worklist.add(succ);
                }
            }

        }
        else if (stmt instanceof If ifStmt)
        {
            CPFact inFact = constants.getInFact(ifStmt);
            ConditionExp condVar = ifStmt.getCondition();
            Value condValue = ConstantPropagation.evaluate(condVar, inFact);
            if(condValue.isConstant())
            {
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(ifStmt))
                {
                    if (edge.getKind() == Edge.Kind.IF_TRUE&&condValue.getConstant() != 0)
                    {
                        worklist.add(edge.getTarget());
                    }
                    else if (edge.getKind() == Edge.Kind.IF_FALSE&&condValue.getConstant() == 0)
                    {
                        worklist.add(edge.getTarget());
                    }
                }
            }
            else
            {
                for (Stmt succ : cfg.getSuccsOf(ifStmt))
                {
                    if (succ != null)
                    {
                        worklist.add(succ);
                    }
                }
            }

        }
        else if (stmt instanceof SwitchStmt switchStmt)
        {

            Var condVar = switchStmt.getVar();
            CPFact inFact = constants.getInFact(switchStmt);
             Value switchValue = ConstantPropagation.evaluate(condVar, inFact);
            if(switchValue.isConstant())
            {

                for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt))
                {
                     if (edge.getKind() == Edge.Kind.SWITCH_CASE&&switchValue.getConstant()==edge.getCaseValue())
                    {
                        worklist.add(edge.getTarget());
                    }
                    else if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT&&!switchStmt.getCaseValues().contains(switchValue.getConstant()))
                    {
                        worklist.add(edge.getTarget());
                    }
                }

            }
            else
            {
                for (Stmt succ : cfg.getSuccsOf(switchStmt))
                {
                    if (succ != null)
                    {
                        worklist.add(succ);
                    }
                }
            }

        }
        else
        {
            for (Stmt succ : cfg.getSuccsOf(stmt))
            {
                if (succ != null)
                {
                    worklist.add(succ);
                }
            }
        }
    }
    for (Stmt stmt : cfg.getNodes())
    {
        if (!liveCode.contains(stmt))
        {
            deadCode.add(stmt);
        }
    }

    //deadCode.remove(cfg.getExit());
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
