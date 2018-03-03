package ir.graph;

import java.util.List;

import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BaseConditional extends BaseStatement implements Conditional {

    protected Statement trueTarget;
    protected Statement falseTarget;
    protected String condition;

    {
        this.isBranch = true;
        this.fallsThrough = true;
    }

    public BaseConditional(String condition) {
        this.condition = condition;
    }

    @Override
    public String getCondition() {
        return this.condition;
    }

    @Override
    public void setCondition(String condition) {
        this.condition = condition;
    }

    @Override
    public Statement getTrueTarget() {
        return this.trueTarget;
    }

    @Override
    public void setTrueTarget(Statement target) {
        this.trueTarget = target;
    }

    @Override
    public Statement getFalseTarget() {
        return this.falseTarget;
    }

    @Override
    public void setFalseTarget(Statement target) {
        this.falseTarget = target;
    }

    @Override
    public List<Variable> getInputVariables() {
        return null;
    }
}
