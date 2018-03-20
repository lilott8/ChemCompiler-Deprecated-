package chemical.epa;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import chemaxon.jep.ChemJEP;
import chemaxon.jep.Evaluator;
import chemaxon.jep.context.MolContext;
import chemaxon.nfunk.jep.ParseException;
import config.ConfigFactory;
import config.InferenceConfig;
import shared.Tuple;

/**
 * Represents an individual group on the EPA Compound Compatibility
 * cheat sheet.  This group has an id, name, and attributes that
 * are defined in the accompanying XML file.
 */
public class Group {

    public static final Logger logger = LogManager.getLogger(Group.class);
    public final String groupName;
    public final int groupId;
    public final ChemTypes chemGroup;
    public final Map<EpaManager.Type, List<Tuple>> attributes = new HashMap<>();
    private List<ChemJEP> evaluators = new ArrayList<>();
    private InferenceConfig config = ConfigFactory.getConfig();


    public Group() {
        this.groupName = "unknown";
        this.groupId = -1;
        this.chemGroup = ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION;
    }

    public Group(int id, String name) {
        this.groupId = id;
        this.groupName = name;
        this.chemGroup = ChemTypes.getTypeFromId(id);
    }

    public Group(int id, String name, Map<EpaManager.Type, List<Tuple>> attributes) {
        this.groupId = id;
        this.groupName = name;
        this.attributes.putAll(attributes);
        this.chemGroup = ChemTypes.getTypeFromId(id);


        Evaluator evaluator = null;
        try {
            evaluator = new Evaluator();
        } catch (ParseException e) {
            logger.error(e.toString());
            return;
        }
        //evaluator.setVerbose(true);
        if (config.buildFilters()) {
            for (Tuple<EpaManager.Type, String> t : this.attributes.get(EpaManager.Type.SMARTS)) {
                try {
                    if (config.smartsLength() == -1) {
                        evaluators.add(evaluator.compile(String.format("match('%s')", t.getRight()), MolContext.class));
                    } else if (t.getRight().length() >= config.smartsLength()) {
                        evaluators.add(evaluator.compile(String.format("match('%s')", t.getRight()), MolContext.class));
                    }
                } catch (Exception e) {
                    logger.error(e.toString());
                }
            }
        }
        //logger.info("Successfully added: " + id + "\t" + success + "/" + total);
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("getId: ").append(this.groupId).append("\t").append("Name: ").append(this.groupName).append("\n");
        for (Map.Entry<EpaManager.Type, List<Tuple>> entry : this.attributes.entrySet()) {
            sb.append(entry.getKey().toString()).append("\n");
            for (Tuple a : entry.getValue()) {
                sb.append(a.toString()).append("\n");
            }
        }
        return sb.toString();
    }

    /**
     * Get the evaluator objects to help classify a compound to this group
     *
     * @return list of evaluators
     */
    public List<ChemJEP> getEvaluators() {
        return evaluators;
    }

    public List<Tuple> getAttributes(EpaManager.Type t) {
        return this.attributes.get(t);
    }

    public enum SearchBy {
        CONTAINS, PREFIX, SUFFIX, MATCHES
    }
}
