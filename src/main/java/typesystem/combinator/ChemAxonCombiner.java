package typesystem.combinator;

import chemaxon.formats.MolExporter;
import chemaxon.struc.Molecule;
import config.ConfigFactory;
import config.InferenceConfig;
import errors.CombinationException;
import shared.substances.ChemAxonCompound;
import shared.substances.BaseCompound;
import typesystem.classification.Classifier;
import typesystem.classification.ClassifierFactory;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemAxonCombiner implements Combiner {

    private InferenceConfig config = ConfigFactory.getConfig();

    private Classifier classifier = ClassifierFactory.getClassifier();

    ChemAxonCombiner() {}

    @Override
    public BaseCompound combine(BaseCompound a, BaseCompound b) {
        ChemAxonCompound compound = null;
        if (this.config.simulateChemistry()) {
            // build a new molecule object
            Molecule molecule = new Molecule();
            ChemAxonCompound compoundA = (ChemAxonCompound) a;
            ChemAxonCompound compoundB = (ChemAxonCompound) b;

            //EpaManager.INSTANCE.validate(a, b);
            // add the first compound
            molecule.fuse(compoundA.getRepresentation());
            // then add the second compound
            molecule.fuse(compoundB.getRepresentation());
            try {
                molecule.aromatize();
            } catch (Exception e) {
            }
            try {
                // We export the SMILES representation to the compound as the name
                compound = new ChemAxonCompound(-1, (String) MolExporter.exportToObject(molecule, "smiles"));
                // and store the molecule with the compound
                compound.setMolecule(molecule);
                // then we classify this new compound
                compound.addReactiveGroup(classifier.classify(compound));
            } catch (Exception e) {
                throw new CombinationException("Cannot combine: " + a.getName() +
                        " with " + b.getName() + "\n" + e.toString());
            }
        } else {
            compound = new ChemAxonCompound(-1);
            compound.addReactiveGroup(a.getReactiveGroups());
            compound.addReactiveGroup(b.getReactiveGroups());
        }
        return compound;
    }
}
