package ir.soot;

import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * Values have a type, they are arguments to instructions,
 *  These manifest as constants or expressions.
 */
public interface Value {

    List<ValueBox> getUseBoxes();

    Set<ChemTypes> getTypes();
}
