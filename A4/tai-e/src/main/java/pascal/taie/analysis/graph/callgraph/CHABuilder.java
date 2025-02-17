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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.IR;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Set<JMethod> visitedMethods = new HashSet<>();
        exploreMethod(entry, callGraph, visitedMethods);
        return callGraph;

    }
    private void exploreMethod(JMethod method, DefaultCallGraph callGraph, Set<JMethod> visitedMethods) {
    if (visitedMethods.contains(method)) {
        return;
    }
    visitedMethods.add(method);
    callGraph.addReachableMethod(method);

    IR ir = method.getIR();
    for (Stmt stmt : ir) {
        if (stmt instanceof Invoke invoke) {
            Set<JMethod> callees = resolve(invoke);
            for (JMethod callee : callees) {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, callee));
                exploreMethod(callee, callGraph, visitedMethods);
            }
        }
    }
}
    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite)
    {
        // TODO - finish me
        Set<JMethod> result = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();
        JClass declaringClass = methodRef.getDeclaringClass();

    if (CallGraphs.getCallKind(callSite) == CallKind.STATIC || CallGraphs.getCallKind(callSite) == CallKind.SPECIAL)
    {
        JMethod method = dispatch(declaringClass, subsignature);
        if (method != null)
        {
            result.add(method);
        }
    }
    else if(CallGraphs.getCallKind(callSite) == CallKind.VIRTUAL || CallGraphs.getCallKind(callSite) == CallKind.INTERFACE)
    {
        Queue<JClass> worklist = new ConcurrentLinkedQueue<>();
        worklist.add(declaringClass);
        while(!worklist.isEmpty())
        {
            JClass jclass = worklist.remove();
            JMethod method = dispatch(jclass, subsignature);
            if(method != null)
            {
                result.add(method);
            }
            if(jclass.isInterface())
            {
                worklist.addAll(hierarchy.getDirectSubinterfacesOf(jclass));
                worklist.addAll(hierarchy.getDirectImplementorsOf(jclass));
            }
            else
            {
                worklist.addAll(hierarchy.getDirectSubclassesOf(jclass));
            }
        }
    }
    else
    {
        assert false : "Unexpected call kind: " + CallGraphs.getCallKind(callSite);
    }
        return result;

    }


    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature)
    {
        // TODO - finish me
        while (jclass != null)
        {
            JMethod method = jclass.getDeclaredMethod(subsignature);
            if (method != null && !method.isAbstract())
            {
                return method;
            }
            jclass = jclass.getSuperClass();
        }
        return null;
    }
}
