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

import fj.test.Arg;
import jas.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

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
        StmtProcessor stmtProcessor = new StmtProcessor();
        if(callGraph.addReachableMethod(method)){
           for(Stmt stmt : method.getIR().getStmts()){
               if(stmt instanceof New neww) stmtProcessor.visit(neww);
               else if(stmt instanceof Copy copy) stmtProcessor.visit(copy);
               else if(stmt instanceof LoadField loadField) stmtProcessor.visit(loadField);
               else if(stmt instanceof StoreField storeField) stmtProcessor.visit(storeField);
               else if(stmt instanceof LoadArray loadArray) stmtProcessor.visit(loadArray);
               else if(stmt instanceof StoreArray storeArray) stmtProcessor.visit(storeArray);
               else if(stmt instanceof Invoke invoke) stmtProcessor.visit(invoke);
           }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me


        @Override
        public Void visit(New stmt) {
            Var x = stmt.getLValue();
            Obj oi = heapModel.getObj(stmt);
            workList.addEntry(pointerFlowGraph.getVarPtr(x),new PointsToSet(oi));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var x = stmt.getLValue();
            Var y = stmt.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(y),pointerFlowGraph.getVarPtr(x));
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {                         // x.f = y    T.f = y
            Var y = stmt.getRValue();
            if(stmt.isStatic()){
                addPFGEdge(pointerFlowGraph.getVarPtr(y),pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            }
            else {
                Optional<LValue> lValue = stmt.getDef();
                if(lValue.isPresent()){
                    if(lValue.get() instanceof Var x){
                        VarPtr xvar = pointerFlowGraph.getVarPtr(x);
                        PointsToSet pts = xvar.getPointsToSet();
                        for(Obj obj : pts) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(y),pointerFlowGraph.getInstanceField(obj,stmt.getFieldRef().resolve()));
                        }
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {                        //x = o.f   x=T.f
            Var x = stmt.getLValue();
            if(stmt.isStatic()){
                addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),pointerFlowGraph.getVarPtr(x));
            }
            else {
                List<RValue> rValues = stmt.getUses();
                RValue rValue = rValues.get(0);
                System.out.println("fuckckck"+stmt);
                System.out.println("rvalueeeeee:"+rValue);
                if(rValue instanceof Var o){
                    VarPtr ovar = pointerFlowGraph.getVarPtr(o);
                    PointsToSet pts = ovar.getPointsToSet();
                    for(Obj obj : pts) {
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj,stmt.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(x));
                    }
                }

            }
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {                   //x = a[..]
//            pointerFlowGraph.getArrayIndex(stmt.getArrayAccess().getIndex();
//            pointerFlowGraph.
//            stmt.getArrayAccess().getBase();
//            stmt.get

            Var lValue = stmt.getLValue();
            PointsToSet all_array = pointerFlowGraph.getVarPtr(stmt.getArrayAccess().getBase()).getPointsToSet();
            for (Obj array : all_array) {
                addPFGEdge(pointerFlowGraph.getArrayIndex(array), pointerFlowGraph.getVarPtr(lValue));
            }
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {                // a[..] = x.

            Var x = stmt.getRValue();
            PointsToSet all_array = pointerFlowGraph.getVarPtr(stmt.getArrayAccess().getBase()).getPointsToSet();
            for (Obj array : all_array) {
                addPFGEdge(pointerFlowGraph.getVarPtr(x),pointerFlowGraph.getArrayIndex(array));
            }

            return null;
        }

        @Override
        public Void visit(Invoke stmt) {                    // x = T.foo()
            if(stmt.isStatic()){
//                JMethod m = hierarchy.dispatch(recv.getType(),invoke.getMethodRef());
//                hierarchy.get
                JMethod m = stmt.getMethodRef().resolve();
                List<Var> params = m.getIR().getParams();
                List<Var> args = stmt.getInvokeExp().getArgs();
                int argcount = stmt.getInvokeExp().getArgCount();
                for(int i =0;i<argcount;i++){
                    addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)),pointerFlowGraph.getVarPtr(params.get(i)));
                }
                Var ret = stmt.getLValue();
                if(ret != null){
                    for(Var retm : m.getIR().getReturnVars()){
                        addPFGEdge(pointerFlowGraph.getVarPtr(retm),pointerFlowGraph.getVarPtr(ret));
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
//        Set<JMethod> visitedMethods = new HashSet<>();
//        Stack<JMethod> wlist = new Stack<>();
//        wlist.add(World.get().getMainMethod());
//        while (!wlist.isEmpty()) {
//            JMethod method = wlist.pop();
//            List<Stmt> stmts = method.getIR().getStmts();
//            for (Stmt stmt : stmts) {
//                if(stmt instanceof Invoke invoke) {
//                    if(!visitedMethods.contains(invoke.getInvokeExp().getMethodRef().resolve())) {
//                        visitedMethods.add(invoke.getInvokeExp().getMethodRef().resolve());
//                        wlist.add(invoke.getInvokeExp().getMethodRef().resolve());
////                        List<Var> args = invoke.getInvokeExp().getArgs();
////                        for(Var arg : args) {
////                            System.out.println(invoke + " arg: " + arg);
////                        }
//                        List<Var> params = invoke.getInvokeExp().getMethodRef().resolve().getIR().getParams();
//                        for(Var param : params) {
//                            System.out.println("param: " + param);
//                        }
//                    }
//                }
//                System.out.println(method +": " + stmt);
//            }
//        }
        // TODO - finish me
//        Set<Pair<Pointer,PointsToSet>> WL = new HashSet<>();
//        World.get().getMainMethod().getIR()

//        Set<JMethod> jMethods = callGraph.getNodes();
//        for(JMethod jMethod : jMethods) {
//            jMethod.getIR().getStmts();
//        }


        while(!workList.isEmpty()){
            WorkList.Entry cur = workList.pollEntry();
            Pointer n = cur.pointer();
            PointsToSet pts = cur.pointsToSet();                                        // remove <n,pts> from WL
//            PointsToSet delta = pts - n.getPointsToSet();
            PointsToSet delta = new PointsToSet();
            for(Obj obj : pts)
                if(!n.getPointsToSet().contains(obj)) delta.addObject(obj);             // delta = pts - pt(n)

            propagate(n,delta);                                                         // propagate(n,delta)

            Set<Stmt> S=new HashSet<>();
            Stream<JMethod> jMethodsS = callGraph.reachableMethods();
            Set<JMethod> jMethods = jMethodsS.collect(Collectors.toSet());
            for(JMethod jMethod : jMethods) {
                for(Stmt stmt : jMethod.getIR().getStmts()) {
                    S.add(stmt);
                }
            }                                                                   // S

            if(n instanceof VarPtr varPtr){                                             // n represent a variable x
                for(Obj oi : delta){
                    List<StoreField> storeFields = varPtr.getVar().getStoreFields();
                    for(StoreField storeField : storeFields){
                        if(S.contains(storeField)){                                     // x.f = y ∈ S
                            Pointer y = pointerFlowGraph.getVarPtr(storeField.getRValue());
                            Pointer oi_f = pointerFlowGraph.getInstanceField(oi,storeField.getFieldAccess().getFieldRef().resolve());
                            addPFGEdge(y,oi_f);
                        }
                    }
                    List<LoadField> loadFields = varPtr.getVar().getLoadFields();
                    for(LoadField loadField : loadFields){
                        if(S.contains(loadField)){                                      // y = x.f ∈ S
                            Pointer y =pointerFlowGraph.getVarPtr(loadField.getLValue());
                            Pointer oi_f = pointerFlowGraph.getInstanceField(oi,loadField.getFieldAccess().getFieldRef().resolve());
                            addPFGEdge(oi_f,y);
                        }
                    }
                    List<LoadArray> loadArrays = varPtr.getVar().getLoadArrays();
                    for(LoadArray loadArray : loadArrays){                              // a = x[..]
                        if(S.contains(loadArray)){
                            Pointer a = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                            Pointer x_star = pointerFlowGraph.getArrayIndex(oi);
                            addPFGEdge(x_star,a);
                        }
                    }
                    List<StoreArray> storeArrays = varPtr.getVar().getStoreArrays();
                    for(StoreArray storeArray : storeArrays){           // x[..] = a
                        if(S.contains(storeArray)){
                            Pointer a = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                            Pointer x_star = pointerFlowGraph.getArrayIndex(oi);
                            addPFGEdge(a,x_star);
                        }
                    }

                    processCall(varPtr.getVar(),oi);
                }
            }
        }


    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet diff = new PointsToSet();
        if(!pointsToSet.isEmpty()){
            for(Obj p:pointsToSet) {
                if(pointer.getPointsToSet().addObject(p))
                    diff.addObject(p);
            }
            for(Pointer s : pointerFlowGraph.getSuccsOf(pointer))
                workList.addEntry(s,pointsToSet);
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
//        Set<Stmt> S=new HashSet<>();
//        Stream<JMethod> jMethodsS = callGraph.reachableMethods();
//        Set<JMethod> jMethods = jMethodsS.collect(Collectors.toSet());
//        for(JMethod jMethod : jMethods) {
//            for(Stmt stmt : jMethod.getIR().getStmts()) {
//                S.add(stmt);
//            }
//        }

        List<Invoke> invokes = var.getInvokes();
        for(Invoke invoke : invokes) {
//            if(S.contains(invoke)){
//                JMethod m = hierarchy.dispatch(recv.getType(),invoke.getMethodRef());
//                hierarchy.get
            JMethod m = resolveCallee(recv,invoke);
            if (m != null) workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()),new PointsToSet(recv));
            else throw new AnalysisException("Cannot find method " + invoke.getMethodRef());

            if(!callGraph.getCalleesOf(invoke).contains(m)){
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m));
                addReachable(m);
                List<Var> params = m.getIR().getParams();
                List<Var> args =invoke.getInvokeExp().getArgs();
                int argCount = invoke.getInvokeExp().getArgCount();
                for(int i = 0 ; i < argCount ; i++){
                    addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                }
                Var lValue = invoke.getLValue();
                if(lValue != null){
                    for(Var ret : m.getIR().getReturnVars()){
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret),pointerFlowGraph.getVarPtr(lValue));
                    }
                }
            }
//            }
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
