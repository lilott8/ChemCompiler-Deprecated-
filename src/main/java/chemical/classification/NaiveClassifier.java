package chemical.classification;

import java.util.Set;

import chemical.epa.ChemTypes;
import shared.substances.BaseCompound;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveClassifier implements Classifier {

    NaiveClassifier() {
    }

    @Override
    public Set<ChemTypes> classify(BaseCompound compound) {
        return compound.getReactiveGroups();
    }
}
