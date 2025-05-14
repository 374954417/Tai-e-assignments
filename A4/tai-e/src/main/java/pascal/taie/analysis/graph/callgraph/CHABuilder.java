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

import static pascal.taie.analysis.graph.callgraph.CallKind.INTERFACE;

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

        IR ir = entry.getIR();         //main函数体的IR
        for(Stmt stmt : ir.getStmts()) {
            if(stmt instanceof Invoke invoke) {
                Set<JMethod> jMethods = resolve(invoke);
                for (JMethod jMethod : jMethods) {
                    callGraph.addReachableMethod(jMethod);
                    Edge<Invoke,JMethod> ee =new Edge<>(INTERFACE,invoke,jMethod);
                    callGraph.addEdge(ee);
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> returnedMethods = new HashSet<>();

//        if(callSite.isStatic()){
//
//        }


        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        JClass declaringClass = callSite.getMethodRef().getDeclaringClass();

        //这里要迭代地拿到所有在hierarchy里的declaringClass的直接以及间接子类

        Collection<JClass> directJclasses = hierarchy.getDirectSubclassesOf(declaringClass);   //拿到直接子类
        Stack<JClass> allsubclasses = new Stack<>();                                           //深度优先搜索第一层
        for (JClass jClass : directJclasses) {
            allsubclasses.push(jClass);
        }
        while (!allsubclasses.isEmpty()) {                                                     //深度优先搜索
            JClass onesubjClass = allsubclasses.pop();
            JMethod jMethod = dispatch(onesubjClass, subsignature);                            //通过dispatch拿到这个类往上层爬最终到达的方法
            Collection<JClass> indirectJclasses = hierarchy.getDirectSubclassesOf(onesubjClass);  //得到这个类的子类
            returnedMethods.add(jMethod);
            for (JClass subsubJclass : indirectJclasses) {
                allsubclasses.push(subsubJclass);
            }
        }
        return returnedMethods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod jMethod = jclass.getDeclaredMethod(subsignature);             //获取本身的类里面subsignature与参数一致的方法
        if(jMethod != null) { return jMethod; }
        else {
            if (jclass.getSuperClass() != null) {                             //如果本身没找到，则往父类找
                return dispatch(jclass.getSuperClass(), subsignature);
            }
        }
        return null;                                                          //最终没找到，返回null
    }
}
