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
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

import static pascal.taie.analysis.graph.callgraph.CallKind.*;

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

        Stack<Invoke> worklist = new Stack<>();


        callGraph.addReachableMethod(entry);                             //main函数的entry
        for(Invoke invoke1 :callGraph.getCallSitesIn(entry)){            //把main函数中的所有函数调用全部插入worklist
            worklist.push(invoke1);
        }

        System.out.println("start!!");

        while(!worklist.empty()) {
            Invoke invoke = worklist.pop();                                                  //如果语句类型是Invoke
            Set<JMethod> jMethods = resolve(invoke);                                        //获取invoke所有callee
            for (JMethod jMethod : jMethods) {                                              //遍历所有callee
                CallKind callKind = CallGraphs.getCallKind(invoke);
                boolean has_change = callGraph.addReachableMethod(jMethod);
                Edge<Invoke,JMethod> ee =new Edge<>(callKind,invoke,jMethod);
                callGraph.addEdge(ee);

                if(has_change && !jMethod.isAbstract()){                                    //如果callee从未遍历到，则把callee函数体中的所有callsite插入worklist
                    for(Invoke invoke1 :callGraph.getCallSitesIn(jMethod)){
                        worklist.push(invoke1);
                    }
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

        if(callSite.isStatic()) {
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            JMethod jMethod = jClass.getDeclaredMethod(subsignature);                             //static只需要在本函数内找
            if(jMethod != null)
                returnedMethods.add(jMethod);
        }
        else if(callSite.isSpecial()) {
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            JMethod jMethod = dispatch(jClass,subsignature);                                     //special需要dispatch一下
            if(jMethod != null)
                returnedMethods.add(jMethod);
        }
        else if(callSite.isInterface()) {
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();

            Set<JClass> visited = new HashSet<>();
            Stack<JClass> worklist = new Stack<>();
            worklist.push(jClass);
            while(!worklist.empty()) {                                                            //interface分两种，遍历时如果遍历到interface，则把所有直接的子interface和impl加入worklist
                JClass jClass1 = worklist.pop();
                if(jClass1.isInterface()) {
                    Collection<JClass> subinterfaces = hierarchy.getDirectSubinterfacesOf(jClass1);
                    for(JClass subinterface : subinterfaces){
                        if(!visited.contains(subinterface)) {
                            worklist.push(subinterface);
                            visited.add(subinterface);
                        }
                    }
                    Collection<JClass> impls = hierarchy.getDirectImplementorsOf(jClass1);

                    for(JClass impl : impls){
                        if(!visited.contains(impl)) {
                            worklist.push(impl);
                            visited.add(impl);
                        }
                    }
                }
                else{                                                                            //如果是类，先把自己加入，再把所有子类加入worklist
                    if(!jClass1.isAbstract())
                        if(dispatch(jClass1, subsignature)!=null)
                            returnedMethods.add(dispatch(jClass1, subsignature));
                    Collection<JClass> subclasses = hierarchy.getDirectSubclassesOf(jClass1);
                    for(JClass subclass : subclasses){
                        if(!visited.contains(subclass)) {
                            worklist.push(subclass);
                            visited.add(subclass);
                        }
                    }
                }
            }


        }
        else if(callSite.isVirtual()) {                                                            //virtual的callee不止一种，需要遍历class hierarchy
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
            Stack<JClass> worklist = new Stack<>();                                           //深度优先搜索第一层
            worklist.push(declaringClass);

            System.out.println("callsite: "+callSite);
            for(JClass jClass : worklist) {
                System.out.println("VirtualJclass in Worklist : "+jClass);
            }
            while (!worklist.isEmpty()) {                                                          //深度优先搜索
                JClass onesubjClass = worklist.pop();
                JMethod jMethod = dispatch(onesubjClass, subsignature);                            //通过dispatch拿到这个类往上层爬最终到达的方法
                if(jMethod != null)
                    returnedMethods.add(jMethod);

                Collection<JClass> indirectJclasses = hierarchy.getDirectSubclassesOf(onesubjClass);  //得到这个类的子类，并把子类压入worklist
                for (JClass subsubJclass : indirectJclasses) {
                    worklist.push(subsubJclass);
                }
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
        if(jMethod != null && !jMethod.isAbstract()) { return jMethod; }                               //如果找到了，直接返回
        else {
            if (jclass.getSuperClass() != null) {                             //如果本身没找到，则往父类找
                return dispatch(jclass.getSuperClass(), subsignature);
            }
        }
        return null;                                                          //最终没找到，返回null
    }
}
