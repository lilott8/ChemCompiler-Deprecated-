package typesystem.classification;

import java.util.Set;

import shared.substances.BaseCompound;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class NaiveClassifier implements Classifier {

    @Override
    public Set<Integer> classify(BaseCompound compound) {
        return compound.getReactiveGroups();
    }
}
