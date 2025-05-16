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
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.*;

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
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me

        CPFact boundaryfact = new CPFact();
        List<Var> vars = cfg.getIR().getParams();
        for (Var var : vars) {
            if(canHoldInt(var)) {
                boundaryfact.update(var, Value.getNAC());
            }
        }
        return boundaryfact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        Set<Var> allVars = new HashSet<>();
        allVars.addAll(fact.keySet());
        allVars.addAll(target.keySet());

        for (Var var : allVars) {
            Value v1 = fact.get(var);    // fact 可能没有 → UNDEF
            Value v2 = target.get(var);  // target 可能没有 → UNDEF
            Value joined = meetValue(v1, v2);

            // 关键：如果 meet 后是 UNDEF，update() 会移除 key
            target.update(var, joined);
        }
    }


    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC()) {return Value.getNAC();}
        else if(v1.isConstant() && v2.isConstant()){
            if(v1.equals(v2)) { return Value.makeConstant(v1.getConstant());}
            else return Value.getNAC();
        }
        else if(v1.isConstant()){return Value.makeConstant(v1.getConstant());}
        else if(v2.isConstant()){return Value.makeConstant(v2.getConstant());}
        else return Value.getUndef();
    }

    public void cl(CPFact fact) {
        fact.clear();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
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
            if(!canHoldInt((Var) lhs)) {return !old.equals(out);}

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
    public static int eval(String op, int v1, int v2) {
        switch (op) {
            case "+": return v1 + v2;
            case "-": return v1 - v2;
            case "*": return v1 * v2;
            case "/": return v1 / v2;
            case "%": return v1 % v2;
            case "|": return v1 | v2;
            case "&": return v1 & v2;
            case "^": return v1 ^ v2;
            case "==": return (v1 == v2) ? 1 : 0;
            case "!=": return (v1 != v2) ? 1 : 0;
            case "<": return (v1 < v2) ? 1 : 0;
            case ">": return (v1 > v2) ? 1 : 0;
            case "<=": return (v1 <= v2) ? 1 : 0;
            case ">=": return (v1 >= v2) ? 1 : 0;
            case "<<": return v1 << v2;
            case ">>": return v1 >> v2;
            case ">>>": return v1 >>> v2;
            default:
                throw new IllegalArgumentException("Unknown operator: " + op);
        }
    }

    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if(exp instanceof BinaryExp) {
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();
            Var v1 = ((BinaryExp) exp).getOperand1();
            Var v2 = ((BinaryExp) exp).getOperand2();

            Value v1_val = in.get(v1);
            Value v2_val = in.get(v2);

            int may_res = 0;

            if(v2_val.isConstant()) {
                if (op.toString().equals("/") || op.toString().equals("%")) {
                    int v2_cons = v2_val.getConstant();
                    if (v2_cons == 0) {
                        return Value.getUndef();
                    }
                }
            }

            if (v1_val.isConstant() && v2_val.isConstant()) {
                int v1_cons = v1_val.getConstant();
                int v2_cons = v2_val.getConstant();
                if (op.toString().equals("/") || op.toString().equals("%")) {
                    if (v2_cons == 0) {
                        return Value.getUndef();
                    }
                }
//                System.out.println("op : " + op);
                may_res = eval(op.toString(), v1_cons, v2_cons);
                return Value.makeConstant(may_res);
            } else {
//                System.out.println("one not constant");
                if (v1_val.isNAC() || v2_val.isNAC()) return Value.getNAC();
                else return Value.getUndef();
            }
        }
        else if(exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if(exp instanceof Var){
            return in.get((Var) exp);
        }

        return Value.getNAC();

    }
}
