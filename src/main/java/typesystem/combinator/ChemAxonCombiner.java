package typesystem.combinator;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import chemaxon.formats.MolExporter;
import chemaxon.struc.Molecule;
import config.ConfigFactory;
import config.InferenceConfig;
import errors.CombinationException;
import shared.substances.ChemAxonCompound;
import shared.substances.BaseCompound;
import typesystem.classification.Classifier;
import typesystem.classification.ClassifierFactory;
import typesystem.epa.ChemTypes;
import typesystem.epa.EpaManager;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemAxonCombiner implements Combiner {

    private InferenceConfig config = ConfigFactory.getConfig();

    private Classifier classifier = ClassifierFactory.getClassifier();

    public static final Logger logger = LogManager.getLogger(ChemAxonCombiner.class);

    ChemAxonCombiner() {}

    @Override
    public ChemAxonCompound combine(BaseCompound a, BaseCompound b) {
        ChemAxonCompound compound = null;
        List<ChemTypes> listA = new ArrayList<>();
        List<ChemTypes> listB = new ArrayList<>();

        listA.addAll(a.getReactiveGroups());
        listB.addAll(b.getReactiveGroups());

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
                //molecule.aromatize();
            } catch (Exception e) {}
            try {
                // We export the SMILES representation to the compound as the name
                compound = new ChemAxonCompound(-1, (String) MolExporter.exportToObject(molecule, "smiles"));
                // and store the molecule with the compound
                compound.setMolecule(molecule);
                // then we classify this new compound
                compound.addReactiveGroup(classifier.classify(compound));
            } catch (Exception e) {
                logger.error("Couldn't combine: " + a + " & " + b);
                // Fail to the naive method, for now.
                compound = new ChemAxonCompound(-1, "null");
                compound.addReactiveGroup(a.getReactiveGroups());
                compound.addReactiveGroup(b.getReactiveGroups());
                return compound;
                //throw new CombinationException("Cannot combine: " + a.getName() +
                //        " with " + b.getName() + "\n" + e.toString());
                //
            }
        } else {
            compound = new ChemAxonCompound(-1);
            compound.addReactiveGroup(a.getReactiveGroups());
            compound.addReactiveGroup(b.getReactiveGroups());
        }
        this.combine(listA, listB);
        return compound;
    }

    @Override
    public Set<ChemTypes> combine(Set<ChemTypes> a, Set<ChemTypes> b) {
        List<ChemTypes> listA = new ArrayList<>();
        List<ChemTypes> listB = new ArrayList<>();

        listA.addAll(a);
        listB.addAll(b);

        this.combine(a, b);

        a.addAll(b);
        return a;
    }
}
