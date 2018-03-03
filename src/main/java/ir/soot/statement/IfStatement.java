package ir.soot.statement;

import ir.soot.Unit;
import ir.soot.UnitBox;
import ir.soot.Value;
import ir.soot.ValueBox;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface IfStatement extends Statement {

    Value getCondition();
    void setCondition(Value condition);
    ValueBox getConditionBox();
    Statement getTarget();
    void setTarget(Unit target);
    UnitBox getTargetBox();

}
