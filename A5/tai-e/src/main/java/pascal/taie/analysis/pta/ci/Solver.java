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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    private Set<JMethod> processedMethods = new HashSet<>();
    private Collection<Stmt> ReachableMethods = new HashSet<>();

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
         if (!processedMethods.add(method)) {
            return;
        }
        callGraph.addReachableMethod(method);
        ReachableMethods.addAll(method.getIR().getStmts());

        for (Stmt stmt : method.getIR().getStmts()) {
            if (stmt instanceof New newStmt) {
                processNewStmt(newStmt);
            } else if (stmt instanceof Copy copyStmt) {
                processCopyStmt(copyStmt);
            } else if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                processStaticStoreField(storeField);
            } else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                processStaticLoadField(loadField);
            } else if (stmt instanceof Invoke invokeStmt && invokeStmt.isStatic()) {
                processStaticInvoke(invokeStmt);
            }
        }
    }
      private void processNewStmt(New stmt)
      {
          if(stmt.getDef().isEmpty())return;
        VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
        Obj obj = heapModel.getObj(stmt);
        PointsToSet pts = new PointsToSet(obj);
        workList.addEntry(varPtr, pts);
      }

    private void processCopyStmt(Copy stmt) {
        VarPtr sourcePtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
        VarPtr targetPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
        addPFGEdge(sourcePtr, targetPtr);
    }

    private void processStaticStoreField(StoreField stmt) {
        JField staticField = stmt.getFieldRef().resolve();
        StaticField targetPtr = pointerFlowGraph.getStaticField(staticField);
        VarPtr sourcePtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
        addPFGEdge(sourcePtr, targetPtr);
    }

    private void processStaticLoadField(LoadField stmt) {
        JField staticField = stmt.getFieldRef().resolve();
        StaticField sourcePtr = pointerFlowGraph.getStaticField(staticField);
        VarPtr targetPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
        addPFGEdge(sourcePtr, targetPtr);
    }

    private void processStaticInvoke(Invoke stmt) {
        JMethod callee = resolveCallee(null, stmt);
        if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, callee)))
        {
            addReachable(callee);

            List<Var> args = stmt.getInvokeExp().getArgs();
            List<Var> params = callee.getIR().getParams();
            for (int i = 0; i < args.size(); i++)
            {
                VarPtr argPtr = pointerFlowGraph.getVarPtr(args.get(i));
                VarPtr paramPtr = pointerFlowGraph.getVarPtr(params.get(i));
                addPFGEdge(argPtr, paramPtr);
            }

            if (stmt.getResult() != null)
            {
                VarPtr resultPtr = pointerFlowGraph.getVarPtr(stmt.getResult());
                for (Var returnVar : callee.getIR().getReturnVars()) {
                    VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                    addPFGEdge(returnVarPtr, resultPtr);
                }
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet sourcePts = source.getPointsToSet();
            if (!sourcePts.isEmpty()) {
                workList.addEntry(target, sourcePts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
         while (!workList.isEmpty())
         {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(pointer, pts);

            if (delta.isEmpty()) {
                continue;
            }

            if (pointer instanceof VarPtr varPtr)
            {
                Var var = varPtr.getVar();
                for (Obj obj : delta)
                {
                    processVarPointer(var, obj);
                }
            }
        }
    }
      private void processVarPointer(Var var, Obj obj)
      {
        for (StoreField storeField : var.getStoreFields()) {
            if (!storeField.isStatic()) {
                JField field = storeField.getFieldRef().resolve();
                InstanceField targetPtr = pointerFlowGraph.getInstanceField(obj, field);
                VarPtr sourcePtr = pointerFlowGraph.getVarPtr(storeField.getRValue());
                addPFGEdge(sourcePtr, targetPtr);
            }
        }

        for (LoadField loadField : var.getLoadFields())
        {
            if (!loadField.isStatic())
            {
                JField field = loadField.getFieldRef().resolve();
                InstanceField sourcePtr = pointerFlowGraph.getInstanceField(obj, field);
                VarPtr targetPtr = pointerFlowGraph.getVarPtr(loadField.getLValue());
                addPFGEdge(sourcePtr, targetPtr);
            }
        }

        for (StoreArray storeArray : var.getStoreArrays())
        {
            VarPtr sourcePtr = pointerFlowGraph.getVarPtr(storeArray.getRValue());
            ArrayIndex targetPtr = pointerFlowGraph.getArrayIndex(obj);
            addPFGEdge(sourcePtr, targetPtr);
        }

        for (LoadArray loadArray : var.getLoadArrays())
        {
            ArrayIndex sourcePtr = pointerFlowGraph.getArrayIndex(obj);
            VarPtr targetPtr = pointerFlowGraph.getVarPtr(loadArray.getLValue());
            addPFGEdge(sourcePtr, targetPtr);
        }

        processCall(var, obj);
    }
    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */

    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
         PointsToSet delta = new PointsToSet();
        PointsToSet pts = pointer.getPointsToSet();

        for (Obj obj : pointsToSet)
        {
            if (pts.addObject(obj))
            {
                delta.addObject(obj);
            }
        }

        if (!delta.isEmpty())
        {
            for(Obj obj : delta . getObjects())
            {
                pointer.getPointsToSet().addObject(obj);
            }
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */

    private void processCall(Var var, Obj recv)
    {
         for (Invoke callSite : var.getInvokes())
        {
            if (!callSite.isStatic())
            {
                JMethod callee = resolveCallee(recv, callSite);
                if (callee == null) {
                    continue;
                }
                PointsToSet recvPts = new PointsToSet(recv);
                workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()), recvPts);
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee)))
                {
                    addReachable(callee);

                    //VarPtr thisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
                    //workList.addEntry(thisPtr, recvPts);

                    List<Var> args = callSite.getInvokeExp().getArgs();
                    List<Var> params = callee.getIR().getParams();
                    for (int i = 0; i < args.size(); i++)
                    {
                        VarPtr argPtr = pointerFlowGraph.getVarPtr(args.get(i));
                        VarPtr paramPtr = pointerFlowGraph.getVarPtr(params.get(i));
                        addPFGEdge(argPtr, paramPtr);
                    }

                    if (callSite.getResult() != null)
                    {
                        VarPtr resultPtr = pointerFlowGraph.getVarPtr(callSite.getResult());
                        for (Var returnVar : callee.getIR().getReturnVars()) {
                            VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                            addPFGEdge(returnVarPtr, resultPtr);
                        }
                    }
                }
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
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
