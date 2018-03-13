package ir.statements;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
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
    protected String scopeName;
    protected List<Statement> trueBranch = new ArrayList<>();
    protected List<Statement> falseBranch = new ArrayList<>();

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
    public String getName() {
        return super.getName() + ": " + this.condition;
    }

    @Override
    public String getScopeName() {
        return this.scopeName;
    }

    @Override
    public void setScopeName(String scopeName) {
        this.scopeName = scopeName;
    }

    public void addTrueBranch(Statement statement) {
        this.trueBranch.add(statement);
    }

    public void addFalseBranch(Statement statement) {
        this.falseBranch.add(statement);
    }

    public List<Statement> getTrueBranch() {
        return trueBranch;
    }

    public List<Statement> getFalseBranch() {
        return falseBranch;
    }
}
