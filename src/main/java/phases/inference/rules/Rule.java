package phases.inference.rules;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/31/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Rule {

    protected InferenceType type;

    public static final Logger logger = LogManager.getLogger(Rule.class);

    public static final String MAT = "mat";
    public static final String REAL = "real";
    public static final String NAT = "nat";
    public static final String CONST = "const";
    public static final String UNKNOWN = "unknown";

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

    // This implicitly allows us to do union sets with MATs
    protected Map<String, Set<String>> constraints = new HashMap<>();

    protected Rule(InferenceType type) {
        this.type = type;
    }

    public Map<String, Set<String>> getConstraints() {
        return constraints;
    }

    public InferenceType getType() {
        return type;
    }

    protected void addConstraints(String key, Set<String> value) {
        if (!this.constraints.containsKey(key)) {
            this.constraints.put(key, new HashSet<>());
        }
        this.constraints.get(key).addAll(value);
    }

    protected void addConstraint(String key, String value) {
        if (!this.constraints.containsKey(key)) {
            this.constraints.put(key, new HashSet<>());
        }
        this.constraints.get(key).add(value);
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
