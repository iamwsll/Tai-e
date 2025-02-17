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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg)
    {
        var fact = new CPFact();
        for(Var param : cfg.getIR().getParams())
        {
            if(canHoldInt(param))
            {
                fact.update(param,Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target)
    {
        fact.forEach((var, value) ->
        {
            target.update(var, meetValue(value, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if(v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        else if(v1.isUndef())
            return v2;
        else if(v2.isUndef())
            return v1;
        else if(v1.getConstant()==v2.getConstant())
            return v1;
        else
            return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        System.err.println("I come to Transfering: ");
        CPFact updated = new CPFact();
        updated.copyFrom(in);
        if(stmt instanceof DefinitionStmt)
        {
            LValue lValue = ((DefinitionStmt<?, ?>) stmt).getLValue();
            RValue rValue = ((DefinitionStmt<?, ?>) stmt).getRValue();
            if(lValue instanceof Var var)
            {
                if(canHoldInt(var))
                {
                    if (evaluate(rValue, in) != null)
                    {
                        updated.update(var, evaluate(rValue, in));
                    };
                }
            }
        }
        System.err.println("I leave Transfering: ");
        return  out.copyFrom(updated);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if(exp instanceof IntLiteral intLiteral)
        {
            return Value.makeConstant(intLiteral.getValue());
        }
        else if(exp instanceof Var var)
        {
            return in.get(var);
        }
        else if (exp instanceof BinaryExp binaryExp)
        {
            Value op1 = evaluate(binaryExp.getOperand1(), in);
            Value op2 = evaluate(binaryExp.getOperand2(), in);
            String op = binaryExp.getOperator().toString();
            if(op2.isConstant()&&op2.getConstant() == 0 &&(op.equals("/")||op.equals("%")))
            {
                return Value.getUndef();
            }
            if(op1.isUndef()||op2.isUndef())return Value.getUndef();
            if(op1.isNAC()||op2.isNAC())return Value.getNAC();

            switch (op)
            {
                case "+":
                    return Value.makeConstant(op1.getConstant() + op2.getConstant());
                case "-":
                    return Value.makeConstant(op1.getConstant() - op2.getConstant());
                case "*":
                    return Value.makeConstant(op1.getConstant() * op2.getConstant());
                case "/":
                    return Value.makeConstant(op1.getConstant() / op2.getConstant());
                case "%":
                    return Value.makeConstant(op1.getConstant() % op2.getConstant());
                case "<":
                    return Value.makeConstant(op1.getConstant() < op2.getConstant() ? 1 : 0);
                case "<=":
                    return Value.makeConstant(op1.getConstant() <= op2.getConstant() ? 1 : 0);
                case ">":
                    return Value.makeConstant(op1.getConstant() > op2.getConstant() ? 1 : 0);
                case ">=":
                    return Value.makeConstant(op1.getConstant() >= op2.getConstant() ? 1 : 0);
                case "==":
                    return Value.makeConstant(op1.getConstant() == op2.getConstant() ? 1 : 0);
                case "!=":
                    return Value.makeConstant(op1.getConstant() != op2.getConstant() ? 1 : 0);
                case "<<":
                    return Value.makeConstant(op1.getConstant() << op2.getConstant());
                case ">>":
                    return Value.makeConstant(op1.getConstant() >> op2.getConstant());
                case ">>>":
                    return Value.makeConstant(op1.getConstant() >>> op2.getConstant());
                case "|":
                    return Value.makeConstant(op1.getConstant() | op2.getConstant());
                case "&":
                    return Value.makeConstant(op1.getConstant() & op2.getConstant());
                case "^":
                    return Value.makeConstant(op1.getConstant() ^ op2.getConstant());
                default:
                    return Value.getUndef();
            }
        }
        else
        {
            return Value.getNAC();
        }
    }
}
