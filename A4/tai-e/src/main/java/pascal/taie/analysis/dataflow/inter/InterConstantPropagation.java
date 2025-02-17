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
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
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

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out)
    {
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact result = new CPFact();
        result.copyFrom(out);
        Stmt src = edge.getSource();
    if (src.getDef().isPresent()&&src instanceof Invoke invoke) {
        Var var = invoke.getResult();
        if (ConstantPropagation.canHoldInt(var))
        {
            result.remove(var);
        }
    }
    return result;
        //return null;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Stmt stmt = edge.getSource();
        CPFact calleeFact = new CPFact();
        Map<Var, Value> paramMapping = new HashMap<>();

    if (stmt instanceof Invoke invoke)
    {
        InvokeExp invokeExp = invoke.getInvokeExp();
        IR calleeIR = edge.getCallee().getIR();

        int cnt = 0;
        for(Var var : calleeIR.getParams())
        {
            Value value = callSiteOut.get(invokeExp.getArg(cnt));
            paramMapping.put(var, value);
            cnt++;
        }
    }
        for (Map.Entry<Var, Value> entry : paramMapping.entrySet())
        {
            calleeFact.update(entry.getKey(), entry.getValue());
        }
        return calleeFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut)
    {
        // TODO - finish me
        CPFact resultFact = new CPFact();
        Stmt callSite = edge.getCallSite();

        if (callSite instanceof Invoke invoke )
        {
            Var lValue = invoke.getLValue();
            if(lValue==null||edge.getReturnVars().isEmpty())
            {
                return resultFact;
            }
             else if(ConstantPropagation.canHoldInt(lValue))
            {
                Value aggregateValue = aggregateReturnValues(returnOut, edge.getReturnVars());
                resultFact.update(lValue, aggregateValue);
            }
        }
        return resultFact;
    }
    private Value aggregateReturnValues(CPFact returnOut, Collection<Var> returnVars)
    {
        Value combinedValue = Value.getUndef();
        for (Var retVar : returnVars)
        {
            Value retValue = returnOut.get(retVar);
            combinedValue = cp.meetValue(combinedValue, retValue);
        }
        return combinedValue;
    }
}
