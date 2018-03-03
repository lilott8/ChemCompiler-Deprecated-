package ir.soot;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface ValueBox {
    void setValue(Value value);

    Value getValue();

    /**
     * Check to see if the value fits in this box.
     * @param value
     * @return true if value fits
     */
    boolean canContainValue(Value value);
}
