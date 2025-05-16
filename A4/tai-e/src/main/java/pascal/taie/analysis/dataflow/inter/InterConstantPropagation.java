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
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Return;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import javax.swing.text.rtf.RTFEditorKit;
import java.util.*;
import java.util.stream.Collectors;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.evaluate;

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
        CPFact old = out.copy();
        Set<Var> keyset = in.keySet();
        out.clear();
        for(Var key : keyset) {
            out.update(key, in.get(key));
        }

        return !old.equals(out);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact old = out.copy();
        Set<Var> keyset = in.keySet();
        out.clear();
        for(Var key : keyset) {
            out.update(key, in.get(key));
        }

        if (stmt instanceof DefinitionStmt<?, ?> defStmt) {
            LValue lhs = defStmt.getLValue(); // 左边变量
            RValue rhs = defStmt.getRValue(); // 右边表达式

            if(lhs == null){return !old.equals(out);}
            if(!(lhs instanceof Var))
            {
                return !old.equals(out);
            }
            if(!ConstantPropagation.canHoldInt((Var) lhs)) {return !old.equals(out);}

            // 分析 RHS
            Value result = evaluate(rhs, in); // 你写一个方法来分析 RHS 值

            // 更新左值
            out.update((Var) lhs, result); // 强转为 Var，前提是你确定它就是 Var 类型
            return !old.equals(out);
        }
        else{
            return !old.equals(out);
        }
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact old = out.copy();

        Optional<LValue> lValue = edge.getSource().getDef();
        if(lValue.isPresent())
            if(lValue.get() instanceof Var var)
                if(ConstantPropagation.canHoldInt(var))
                    old.update(var,Value.getUndef());
        return old;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact after = new CPFact();
        int arg_count = ((Invoke) edge.getSource()).getInvokeExp().getArgCount();
        for(int i = 0; i < arg_count; i++) {
            Var arg = ((Invoke) edge.getSource()).getInvokeExp().getArg(i);
            Var param = edge.getCallee().getIR().getParam(i);
            if(ConstantPropagation.canHoldInt(param))
                after.update(param, callSiteOut.get(arg));
        }

        return after;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact after = new CPFact();

        Optional<LValue> lValue = edge.getCallSite().getDef();
        if(lValue.isPresent())
            if(lValue.get() instanceof Var var)
                if(ConstantPropagation.canHoldInt(var)) {
                    Collection<Var> ret_vars_collection = edge.getReturnVars();
                    Set<Var> ret_vars = new HashSet<>(ret_vars_collection);

                    Value ret_value = Value.getUndef();
                    for(Var ret_var : ret_vars) {
                        ret_value = cp.meetValue(ret_value,returnOut.get(ret_var));
                    }

                    after.update(var, ret_value);
                }
        return after;
    }
}
