package ir.graph;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.List;

import shared.variable.Variable;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BaseConditional extends BaseStatement implements Conditional {

    public static final Logger logger = LogManager.getLogger(BaseConditional.class);

    protected Statement trueTarget;
    protected Statement falseTarget;
    protected String condition;

    {
        this.isBranch = true;
        this.fallsThrough = true;
    }

    public BaseConditional(String name, String condition) {
        super(name);
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

    @Override
    public void setTrueTarget(Block block) {
        logger.warn("setTrueTarget(Block block) is not implemented");
    }
}
