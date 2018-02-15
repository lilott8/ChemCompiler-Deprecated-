package chemical.classification;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import chemaxon.jep.ChemJEP;
import chemaxon.jep.context.MolContext;
import chemaxon.nfunk.jep.ParseException;
import chemaxon.struc.Molecule;
import config.ConfigFactory;
import config.InferenceConfig;
import shared.substances.ChemAxonCompound;
import shared.substances.BaseCompound;
import chemical.epa.ChemTypes;
import chemical.epa.EpaManager;
import chemical.epa.Group;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemAxonClassifier implements Classifier {

    public static final Logger logger = LogManager.getLogger(Classifier.class);
    private InferenceConfig config = ConfigFactory.getConfig();

    ChemAxonClassifier() {}

    @Override
    public Set<ChemTypes> classify(BaseCompound a) {
        Set<ChemTypes> results = new HashSet<>();
        // Translate the compound.
        ChemAxonCompound compound = (ChemAxonCompound) a;
        if (this.config.simulateChemistry()) {
            Molecule molecule = compound.getRepresentation();
            MolContext context = new MolContext();
            context.setMolecule(compound.getRepresentation());
            if (molecule != null) {
                try {
                    // Don't go in here if we don't have filters.
                    if (this.config.buildFilters()) {
                        // for all the groups in the EPA map
                        for (Map.Entry<ChemTypes, Group> entry : EpaManager.INSTANCE.groupMap.entrySet()) {
                            // for every evaluator in the group
                            for (ChemJEP jep : entry.getValue().getEvaluators()) {
                                // see if the SMARTS is represented in the SMILES
                                if (jep.evaluate_boolean(context)) {
                                    // if it is, we add it to the results
                                    results.add(entry.getKey());
                                }
                            }
                        }
                    }
                } catch (ParseException e) {
                    logger.error(e);
                }
            } else {
                logger.info("We don't have molecular information for this chemical.");
            }
            // if we have nothing, then we don't know how to classify it
            if (results.size() == 0) {
                results.add(ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
            }
        } else {
            results.addAll(compound.getReactiveGroups());
        }
        return results;
    }
}
