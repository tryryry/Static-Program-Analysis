/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2020-- Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2020-- Yue Li <yueli@nju.edu.cn>
 * All rights reserved.
 *
 * Tai-e is only for educational and academic purposes,
 * and any form of commercial use is disallowed.
 * Distribution of Tai-e is disallowed without the approval.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Objects;

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
        //return null;
        CPFact cpFact=new CPFact();
        for(Var var:cfg.getMethod().getIR().getParams()){
            if(canHoldInt(var)){
                cpFact.update(var,Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        //return null;
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var:fact.keySet()){
            target.update(var,meetValue(fact.get(var),target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        //return null;
        Value v = null;
        if(v1.isNAC()||v2.isNAC()){
            v=Value.getNAC();
        }else if(v1.isUndef()){
            v=v2;
        }else if(v2.isUndef()){
            v=v1;
        }else if(v1.isConstant()&&v2.isConstant()){
            if(v1.getConstant()==v2.getConstant()){
                v=v1;
            }else{
                v=Value.getNAC();
            }
        }
        return v;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact temp=in.copy();

        DefinitionStmt def = null;
        Value value = null;
        if(stmt instanceof DefinitionStmt){
            def=(DefinitionStmt) stmt;
            Exp exp=def.getRValue();
            value=evaluate(exp,in);
            Exp expL=def.getLValue();
            Var v = null;
            if(expL instanceof Var){
                v=(Var)expL;
                if(canHoldInt(v)){
                    temp.update(v,value);
                }
                //temp.remove(v);

            }
            return out.copyFrom(temp);
        }
        return out.copyFrom(in);

        //return false;
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
        // TODO - finish me
        //return null;
        if(exp instanceof Var){
            Var v=(Var)exp;
            if(canHoldInt(v)){
                if(in.get(v).isConstant()){
                    return Value.makeConstant(in.get(v).getConstant());
                }
                else{
                    return Value.getUndef();
                }
            }
        }else if(exp instanceof IntLiteral){
            IntLiteral i=(IntLiteral) exp;
            return Value.makeConstant(i.getValue());

        }else if(exp instanceof BinaryExp){
            BinaryExp bExp=(BinaryExp) exp;
            Var v1=bExp.getOperand1();
            Var v2=bExp.getOperand2();
            if(!(canHoldInt(v1)||canHoldInt(v2))){
                return Value.getNAC();
            }
            if(in.get(v1).isConstant()&&in.get(v2).isConstant()){

                int const1=in.get(v1).getConstant();
                int const2=in.get(v2).getConstant();
                if(Objects.equals(bExp.getOperator().toString(), "+")){
                    return Value.makeConstant(const1+const2);
                }else if(Objects.equals(bExp.getOperator().toString(), "-")){
                    return Value.makeConstant(const1-const2);
                }else if(Objects.equals(bExp.getOperator().toString(), "*")){
                    return Value.makeConstant(const1*const2);
                }else if(Objects.equals(bExp.getOperator().toString(), "/")){
                    if(const2==0){
                        //System.out.println("Hello");
                        return Value.getUndef();
                    }
                    return Value.makeConstant(const1/const2);
                }else if(Objects.equals(bExp.getOperator().toString(), "%")){
                    if(const2==0){
                        return Value.getUndef();
                    }
                    return Value.makeConstant(const1%const2);
                }else if(Objects.equals(bExp.getOperator().toString(), "&")){
                    return Value.makeConstant(const1&const2);
                }else if(Objects.equals(bExp.getOperator().toString(), "|")){
                    return Value.makeConstant(const1|const2);
                }else if(Objects.equals(bExp.getOperator().toString(), "^")){
                    return Value.makeConstant(const1^const2);
                }else if(Objects.equals(bExp.getOperator().toString(), "==")){
                    int cond=0;
                    if(const1==const2)cond=1;
                    return Value.makeConstant(cond);
                }else if(Objects.equals(bExp.getOperator().toString(), "!=")){
                    int cond=0;
                    if(const1!=const2)cond=1;
                    return Value.makeConstant(cond);
                }else if(Objects.equals(bExp.getOperator().toString(), "<")){
                    int cond=0;
                    if(const1<const2)cond=1;
                    return Value.makeConstant(cond);
                }else if(Objects.equals(bExp.getOperator().toString(), ">")){
                    int cond=0;
                    if(const1>const2)cond=1;
                    return Value.makeConstant(cond);
                }else if(Objects.equals(bExp.getOperator().toString(), "<=")){
                    int cond=0;
                    if(const1<=const2)cond=1;
                    return Value.makeConstant(cond);
                }else if(Objects.equals(bExp.getOperator().toString(), ">=")){
                    int cond=0;
                    if(const1>=const2)cond=1;
                    return Value.makeConstant(cond);
                }else if(Objects.equals(bExp.getOperator().toString(), "<<")) {
                    return Value.makeConstant(const1 << const2);
                }
                else if(Objects.equals(bExp.getOperator().toString(), ">>")) {
                    return Value.makeConstant(const1 >> const2);
                }else if(Objects.equals(bExp.getOperator().toString(), ">>>")) {
                    return Value.makeConstant(const1 >>> const2);
                }
            }else if(in.get(v1).isNAC()||in.get(v2).isNAC()){
                if(Objects.equals(bExp.getOperator().toString(), "%")||Objects.equals(bExp.getOperator().toString(), "/")) {
                    if(in.get(v2).isConstant()&&in.get(v2).getConstant()==0){
                        return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }else{
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
