package ir.graph;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Conditional extends Statement {

    String getCondition();

    void setCondition(String condition);
    Statement getTrueTarget();
    void setTrueTarget(Statement target);
    Statement getFalseTarget();
    void setFalseTarget(Statement target);
    void setTrueTarget(Block block);
}
