package ir.soot.statement;

import java.util.List;

import ir.soot.InvokeExpression;
import ir.soot.Unit;
import ir.soot.UnitBox;
import ir.soot.Value;
import ir.soot.ValueBox;
import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 2/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Branch implements IfStatement {

    ValueBox condition;
    UnitBox target;

    public Branch() {

    }

    public Branch(Value condition, Unit target) {
        this(condition, (UnitBox) target);
    }

    public Branch(Value condition, UnitBox target) {
        this((ValueBox) condition, target);
    }

    public Branch(ValueBox condition, UnitBox target) {
        this.condition = condition;
        this.target = target;
    }

    @Override
    public Value getCondition() {
        return this.condition.getValue();
    }

    @Override
    public void setCondition(Value condition) {
        this.condition.setValue(condition);
    }

    @Override
    public ValueBox getConditionBox() {
        return this.condition;
    }

    @Override
    public Statement getTarget() {
        return (Statement) this.target.getUnit();
    }

    @Override
    public void setTarget(Unit target) {
        this.target.setUnit(target);
    }

    @Override
    public UnitBox getTargetBox() {
        return this.target;
    }

    @Override
    public boolean containsInvokeExpression() {
        return false;
    }

    @Override
    public InvokeExpression getInvokeExpression() {
        return null;
    }

    @Override
    public ValueBox getInvokeExpressionBox() {
        return null;
    }

    @Override
    public boolean containsFieldRef() {
        return false;
    }

    @Override
    public void getFieldRef() {

    }

    @Override
    public ValueBox getFieldRefBox() {
        return null;
    }

    /**
     * Returns a list of boxes containing values used in this unit.
     */
    @Override
    public List<ValueBox> getUseBoxes() {
        return null;
    }

    /**
     * Returns a list of boxes containing values defined in this unit.
     */
    @Override
    public List<ValueBox> getDefBoxes() {
        return null;
    }

    /**
     * Returns a list of Boxes containing units defined in this unit;
     * This is usually branch targets.
     */
    @Override
    public List<UnitBox> getUnitBoxes() {
        return null;
    }

    /**
     * Adds a box to this list.
     */
    @Override
    public void addBoxPointingToThis(UnitBox box) {

    }

    /**
     * Removes a box that points to this box.
     */
    @Override
    public void removeBoxPointingToThis(UnitBox box) {

    }

    /**
     * Clear anything pointing to this box.
     */
    @Override
    public void clearUnitBoxes() {

    }

    /**
     * Returns the list of uses/defs in this box.
     *
     * @return list
     */
    @Override
    public List<ValueBox> getUseAndDefBoxes() {
        return null;
    }

    /**
     * Returns true if execution after this statement will continue at following statement.
     */
    @Override
    public boolean fallsThrough() {
        return false;
    }

    /**
     * Returns true if execution after this statement does not continue to following statement.
     * This is for branches.
     *
     * @return boolean
     */
    @Override
    public boolean branches() {
        return false;
    }

    public String toJSON() {
        return null;
    }

    public String compose(Formula instruction) {
        return null;
    }

    public String compose(Variable variable) {
        return null;
    }
}
