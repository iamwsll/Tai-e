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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver
{

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector)
    {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve()
    {
        initialize();
        analyze();
    }

    private void initialize()
    {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod)
    {
        // TODO - finish me
        if (!callGraph.contains(csMethod))
        {
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().stmts().forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target)
    {
        // TODO - finish me
        if (pointerFlowGraph.getSuccsOf(source).contains(target))
            return;
        pointerFlowGraph.addEdge(source, target);
        workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze()
    {
        // TODO - finish me
        while (!workList.isEmpty())
        {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if (delta.isEmpty())
                continue;

            if (entry.pointer() instanceof CSVar csVar)
            {
                delta.forEach(obj ->
                {
                    Var varriable = csVar.getVar();
                    Context context = csVar.getContext();

                    varriable.getStoreFields().forEach(storeField ->
                            addPFGEdge(csManager.getCSVar(context, storeField.getRValue()),
                                    csManager.getInstanceField(obj, storeField.getFieldAccess().getFieldRef().resolve())));

                    varriable.getLoadFields().forEach(loadField -> addPFGEdge(csManager.getInstanceField(obj, loadField.getFieldAccess().getFieldRef().resolve()),
                            csManager.getCSVar(context, loadField.getLValue())));

                    varriable.getStoreArrays().forEach(storeArray -> addPFGEdge(csManager.getCSVar(context, storeArray.getRValue()), csManager.getArrayIndex(obj)));

                    varriable.getLoadArrays().forEach(loadArray -> addPFGEdge(csManager.getArrayIndex(obj), csManager.getCSVar(context, loadArray.getLValue())));

                    processCall(csVar, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet)
    {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet)
        {
            if (pointer.getPointsToSet().contains(obj))
                continue;
            pointer.getPointsToSet().addObject(obj);
            delta.addObject(obj);
        }

        if (!delta.isEmpty())
        {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer))
            {
                workList.addEntry(succ, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj)
    {
        // TODO - finish me
        Context currentContext = recv.getContext();
        for (Invoke invokeSite : recv.getVar().getInvokes())
        {
            JMethod resolvedMethod = resolveCallee(recvObj, invokeSite);

            if (resolvedMethod == null) continue;

            CSCallSite invokeElement = csManager.getCSCallSite(currentContext, invokeSite);
            Context calleeCtx = contextSelector.selectContext(invokeElement, recvObj, resolvedMethod);
            CSMethod calleeMethod = csManager.getCSMethod(calleeCtx, resolvedMethod);

            PointsToSet recvPointsTo = PointsToSetFactory.make(recvObj);
            Pointer calleeThis = csManager.getCSVar(calleeCtx, resolvedMethod.getIR().getThis());
            workList.addEntry(calleeThis, recvPointsTo);

            if (callGraph.getCalleesOf(invokeElement).contains(calleeMethod)) continue;
            addReachable(calleeMethod);
            callGraph.addEdge(
                    new Edge<>(
                            CallGraphs.getCallKind(invokeElement.getCallSite()),
                            invokeElement,
                            calleeMethod
                    )
            );

            Context callerCtx = invokeElement.getContext();
            Context calleeCtx1 = calleeMethod.getContext();
            List<Var> actualParameters = invokeElement.getCallSite().getInvokeExp().getArgs();
            List<Var> formalParameters = calleeMethod.getMethod().getIR().getParams();

            for (int idx = 0; idx < actualParameters.size(); idx++)
            {
                Pointer from = csManager.getCSVar(callerCtx, actualParameters.get(idx));
                Pointer to = csManager.getCSVar(calleeCtx1, formalParameters.get(idx));
                addPFGEdge(from, to);
            }

            Var callLValue = invokeElement.getCallSite().getLValue();
            if (callLValue == null) continue;

            for (Var retVar : calleeMethod.getMethod().getIR().getReturnVars())
            {
                Pointer retPtr = csManager.getCSVar(calleeCtx1, retVar);
                Pointer callerRetPtr = csManager.getCSVar(callerCtx, callLValue);
                addPFGEdge(retPtr, callerRetPtr);
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite)
    {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult()
    {
        if (result == null)
        {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void>
    {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod)
        {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt)
        {
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), PointsToSetFactory.make(csManager.getCSObj(heapContext, obj)));
            return null;
        }

        public Void visit(Copy stmt)
        {
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        public Void visit(LoadField stmt)
        {
            // 静态字段
            if (stmt.getRValue() instanceof StaticFieldAccess)
            {
                addPFGEdge(csManager.getStaticField(stmt.getRValue().getFieldRef().resolve()), csManager.getCSVar(context, stmt.getLValue()));
            }
            return null;
        }

        public Void visit(StoreField stmt)
        {
            if (stmt.getLValue() instanceof StaticFieldAccess)
            {
                addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getStaticField(stmt.getLValue().getFieldRef().resolve()));
            }
            return null;
        }

        public Void visit(Invoke stmt)
        {
            // 静态调用
            if (stmt.isStatic())
            {
                ;
                JMethod method = resolveCallee(null, stmt);
                Context contextCallee = contextSelector.selectContext(csManager.getCSCallSite(context, stmt), method);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                CSMethod csMethod1 = csManager.getCSMethod(contextCallee, method);
                if (!callGraph.getCalleesOf(csCallSite).contains(csMethod1))
                {
                    addReachable(csMethod1);
                    callGraph.addEdge(
                            new Edge<>(
                                    CallGraphs.getCallKind(csCallSite.getCallSite()),
                                    csCallSite,
                                    csMethod1
                            )
                    );
                    Context callerCtx = csCallSite.getContext();
                    Context calleeCtx = csMethod1.getContext();
                    List<Var> actualParameters = csCallSite.getCallSite().getInvokeExp().getArgs();
                    List<Var> formalParameters = csMethod1.getMethod().getIR().getParams();
                    for (int idx = 0; idx < actualParameters.size(); idx++)
                    {
                        Pointer from = csManager.getCSVar(callerCtx, actualParameters.get(idx));
                        Pointer to = csManager.getCSVar(calleeCtx, formalParameters.get(idx));
                        addPFGEdge(from, to);
                    }
                    Var callLValue = csCallSite.getCallSite().getLValue();
                    if (callLValue != null)
                    {
                        for (Var retVar : csMethod1.getMethod().getIR().getReturnVars())
                        {
                            Pointer retPtr = csManager.getCSVar(calleeCtx, retVar);
                            Pointer callerRetPtr = csManager.getCSVar(callerCtx, callLValue);
                            addPFGEdge(retPtr, callerRetPtr);
                        }
                    }
                }

            }
            return null;
        }

        public Void visit(StoreArray stmt)
        {
            // 对数组存储不在此处理
            return null;
        }

        public Void visit(LoadArray stmt)
        {
            return null;
        }
    }
}
