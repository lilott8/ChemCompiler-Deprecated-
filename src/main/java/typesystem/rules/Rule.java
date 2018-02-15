package typesystem.rules;


import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import config.ConfigFactory;
import config.InferenceConfig;
import typesystem.Inference.InferenceType;
import typesystem.elements.Instruction;
import shared.Variable;
import chemical.epa.ChemTypes;
import chemical.identification.IdentifierFactory;

/**
 * @created: 7/31/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Rule {

    public enum InstructionType {
        ASSIGN, DETECT, HEAT, BRANCH, MIX, SPLIT, OUTPUT, STATIONARY, LOOP, FUNCTION, MANIFEST, DRAIN, MODULE
    }

    protected InferenceType type;

    protected final Logger logger;

    protected InferenceConfig config = ConfigFactory.getConfig();

    // Keep track of the instruction id to input/outputs
    protected static Map<Integer, Instruction> instructions = new LinkedHashMap<>();
    protected static Map<String, Variable> variables = new HashMap<>();

    protected Rule(InferenceType type) {
        this.type = type;
        this.logger = LogManager.getLogger(Rule.class);
    }
    protected Rule(InferenceType type, Class<? extends Rule> clazz) {
        this.type = type;
        logger = LogManager.getLogger(clazz);
    }

    public InferenceType getType() {
        return type;
    }

    public Map<String, Variable> getVariables() {
        return variables;
    }

    public Map<Integer, Instruction> getInstructions() {
        return instructions;
    }

    protected static void addInstruction(Instruction i) {
        instructions.put(i.getId(), i);
    }

    protected static void addVariable(Variable t) {
        if (!variables.containsKey(t.getVarName())) {
            variables.put(t.getVarName(), t);
        } else {
            if (variables.get(t.getVarName()).equals(t)) {
            }
        }
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

    protected Set<ChemTypes> getTypingConstraints(Variable input) {
        if (variables.containsKey(input.getVarName())) {
            return variables.get(input.getVarName()).getTypingConstraints();
        } else {
            return IdentifierFactory.getIdentifier().identifyCompoundForTypes(input.getVarName());
        }
    }

    public static String createHash(String input) {
        Logger log = LogManager.getLogger(Rule.class);
        try {
            MessageDigest digest = MessageDigest.getInstance("MD5");
            byte[] bytes = digest.digest(input.getBytes());
            StringBuffer sb = new StringBuffer();
            int x = 0;
            for (byte b : bytes) {
                sb.append(String.format("%02x", b));
                x++;
            }
            if (Rule.isNumeric(Character.toString(sb.charAt(0)))) {
                sb.insert(0, "a");
            }
            return sb.toString();
        } catch(NoSuchAlgorithmException e) {
            input = "a" + input;
            return input;
        }
    }

    public static boolean isMaterial(String value) {
        return true;
    }
}
