package ir.soot;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface UnitBox {
    void setUnit(Unit unit);

    Unit getUnit();

    boolean canContainUnit(Unit unit);

    /**
     * Returns true is the UnitBox is holding a unit that
     *  is a target of a branch.
     * @return
     */
    boolean isBranchTarget();
}
