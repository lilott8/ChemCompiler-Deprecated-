package typesystem.classification;

import java.util.Set;

import shared.substances.BaseCompound;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveClassifier implements Classifier {

    NaiveClassifier() {}

    @Override
    public Set<ChemTypes> classify(BaseCompound compound) {
        return (Set<ChemTypes>) compound.getReactiveGroups();
    }
}
