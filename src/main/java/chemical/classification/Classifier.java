package chemical.classification;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.substances.BaseCompound;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Classifier {

    Set<ChemTypes> classify(BaseCompound compound);
}
