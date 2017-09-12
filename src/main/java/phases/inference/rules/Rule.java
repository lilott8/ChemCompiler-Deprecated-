package phases.inference.rules;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import config.ConfigFactory;
import config.InferenceConfig;
import phases.inference.ChemTypes;
import phases.inference.SMTConstraint;
import phases.inference.Inference.InferenceType;
import phases.inference.Constraint;

/**
 * @created: 7/31/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Rule {

    protected InferenceType type;

    protected final Logger logger;

    public final String CONST = "constant";

    public static final Set<String> operands = new HashSet<String>(){{
        add("==");
        add(">=");
        add("<=");
        add("!=");
        add("&&");
        add("||");
        add("!");
        add("and");
        add("AND");
        add("or");
        add("OR");
        add("not");
        add("NOT");
    }};

    protected InferenceConfig config = ConfigFactory.getConfig();

    // This implicitly allows us to do union sets with types
    protected Map<String, Constraint> constraints = new HashMap<>();

    protected Rule(InferenceType type) {
        this.type = type;
        this.logger = LogManager.getLogger(Rule.class);
    }
    protected Rule(InferenceType type, Class<? extends Rule> clazz) {
        this.type = type;
        logger = LogManager.getLogger(clazz);
    }

    public Map<String, Constraint> getConstraints() {
        return constraints;
    }

    public InferenceType getType() {
        return type;
    }

    protected void addConstraints(String key, Set<ChemTypes> value) {
        if (!constraints.containsKey(key)) {
            constraints.put(key, new SMTConstraint(key));
        }
        constraints.get(key).addConstraints(value);
    }

    protected void addConstraint(String key, ChemTypes value) {
        if (!constraints.containsKey(key)) {
            constraints.put(key, new SMTConstraint(key));
        }
        constraints.get(key).addConstraint(value);
    }

    public static boolean isNumeric(String value) {
        return Rule.isNaturalNumber(value) || Rule.isRealNumber(value);
    }

    public static boolean isNaturalNumber(String value) {
        try {
            Integer.parseInt(value);
            return true;
        } catch (NumberFormatException e) {
            return false;
        }
    }

    public static boolean isRealNumber(String value) {
        try {
            Float.parseFloat(value);
            return true;
        } catch(NumberFormatException e) {
            return false;
        }
    }

    public static boolean isMaterial(String value) {
        return true;
    }
}
