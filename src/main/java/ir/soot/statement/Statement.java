package ir.soot.statement;


import ir.soot.InvokeExpression;
import ir.soot.Unit;
import ir.soot.ValueBox;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Statement extends Unit {

    boolean containsInvokeExpression();
    InvokeExpression getInvokeExpression();
    ValueBox getInvokeExpressionBox();

    boolean containsFieldRef();
    void getFieldRef();
    ValueBox getFieldRefBox();

}
