package ir.soot;

import java.util.List;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Unit {
    /**
     * Returns a list of boxes containing values used in this unit.
     * @return
     */
    List<ValueBox> getUseBoxes();

    /**
     * Returns a list of boxes containing values defined in this unit.
     * @return
     */
    List<ValueBox> getDefBoxes();

    /**
     * Returns a list of Boxes containing units defined in this unit;
     *  This is usually branch targets.
     * @return
     */
    List<UnitBox> getUnitBoxes();

    /**
     * Adds a box to this list.
     * @param box
     */
    void addBoxPointingToThis(UnitBox box);

    /**
     * Removes a box that points to this box.
     * @param box
     */
    void removeBoxPointingToThis(UnitBox box);

    /**
     * Clear anything pointing to this box.
     */
    void clearUnitBoxes();

    /**
     * Returns the list of uses/defs in this box.
     * @return list
     */
    List<ValueBox> getUseAndDefBoxes();

    /**
     * Returns true if execution after this statement will continue at following statement.
     * @return
     */
    boolean fallsThrough();

    /**
     * Returns true if execution after this statement does not continue to following statement.
     *  This is for branches.
     * @return boolean
     */
    boolean branches();
}
