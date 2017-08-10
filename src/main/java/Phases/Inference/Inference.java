package Phases.Inference;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.reflections.Reflections;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.InstructionNode;
import Phases.Inference.Rules.InferenceRule;
import Phases.Inference.Rules.Rule;
import Phases.Phase;
import Shared.Tuple;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * Because it is too cumbersome to implement a `Visitor` pattern here,
 *  we just rely on the base constructs that exists...
 *
 *  We rely on annotations to dynamically load any inference rules and
 *  then associate those with their instruction within the compiler.
 */
public class Inference implements Phase {

    // Enum to determine what type the node in the CFG is.
    public enum InferenceType {
        TERM, INSTRUCTION
    }

    // Logging mechanism.
    public static final Logger logger = LogManager.getLogger(Inference.class);

    // Package for where to look for annotated rules.
    public static final String INFERENCE_PACKAGE = "Phases.Inference.Rules";

    // This maps the rule name the corresponding rule.
    private final Map<String, Rule> inferenceRules = new HashMap<>();

    // This maps each instruction/term to the constraints that it has.
    private Map<String, Set<String>> constraints = new HashMap<String, Set<String>>();

    // This is for human readability and testing only.  This will be removed for production.
    private Map<Tuple<String, String>, Set<String>> testingConstraints = new HashMap<Tuple<String, String>, Set<String>>();

    // Control flow graph needed to infer types from.
    private CFG controlFlowGraph;

    // Default Constructor
    public Inference() {
        this.loadRules();
        for(Map.Entry<String, Rule> entry : this.inferenceRules.entrySet()) {
            logger.info(entry.getKey());
        }
    }

    /**
     * Run the inference phase of the compilation process.
     * @param controlFlowGraph
     */
    public void runPhase(CFG controlFlowGraph) {
        this.controlFlowGraph = controlFlowGraph;
        // Iterate the CFG.
        for(Map.Entry<Integer, BasicBlock> block : this.controlFlowGraph.getBasicBlocks().entrySet()) {
            // Iterate the instructions.
            for(InstructionNode node : block.getValue().getInstructions()) {
                // If we have an instruction, see what we can infer.
                if(node.Instruction() != null) {
                    // This will give us the typing of all the constraints in the instruction.
                    this.addConstraints(this.inferConstraint(StringUtils.upperCase(node.Instruction().getClassification()), node));
                }
                // logger.info(node.Instruction());
            }
        }

        logger.info(this.constraints.toString());
    }

    /**
     * Infer the constraint from the instruction.
     * @param name
     *   Name of the instruction.
     * @param instruction
     *   Instruction to be inferred.
     * @return
     *   A mapping of id to what was inferred.
     */
    public Map<String, Set<String>> inferConstraint(String name, InstructionNode instruction) {
        if(this.inferenceRules.containsKey(name)) {
            Rule rule = this.inferenceRules.get(name);

            /*
             * Temp = Mix x with y for n
             *  ^def_use  |      |     |
             *         get_use   |     |
             *                get_use  |
             *                      property
             */
            // These are the defs on instruction
            for(String out : instruction.get_def()) {
                rule.gatherDefConstraints(out);
            }

            // This is the input to the instruction
            for(String in: instruction.get_use()) {
                rule.gatherUseConstraints(in);
            }

            // Get the properties of the instruction if they exist
            for (Property prop : instruction.Instruction().getProperties()) {
                rule.gatherConstraints(prop);
            }

            logger.debug("Id: " + instruction.ID());
            logger.debug("Classification: " + instruction.Instruction().getClassification());
            logger.debug("Input Symbols: " + instruction.getInputSymbols());
            logger.debug("Properties: " + instruction.Instruction().getProperties());
            logger.debug("Use: " + instruction.get_use());
            logger.debug("Def: " + instruction.get_def());
            logger.debug("Output Symbols: " + instruction.getOutputSymbols());
            logger.debug("toString(): " + instruction.toString());
            logger.warn("=================================");


            // return the constraints from the rule
            return rule.getConstraints();
            //return this.inferenceRules.get(name).gatherConstraints(instruction).getConstraints();
        }
        logger.warn("We don't have a rule for: " + name);
        // return an empty array list for ease.
        return new HashMap<String, Set<String>>();
    }

    /**
     * Allows adding of constraints to terms/instructions
     * @param constraints
     *   HashSet of constraints
     */
    private void addConstraints(Map<String, Set<String>> constraints) {
        // If the constraints are empty, don't do anything
        if(constraints == null || constraints.isEmpty()) {
            return;
        }

        // Otherwise add all constraints to the appropriate key.
        for (Map.Entry<String, Set<String>> entry : constraints.entrySet()) {
            if (!this.constraints.containsKey(entry.getKey())) {
                this.constraints.put(entry.getKey(), new HashSet<String>());
            }

            this.constraints.get(entry.getKey()).addAll(entry.getValue());
        }
    }

    /**
     * @return
     *   String representation.
     */
    public String toString() {
        return super.toString() + this.constraints.toString();
    }

    /**
     * Load the rules from the annotation provided.
     * This will load the classes, instantiate them and prepare
     * the rules for use when ready.
     */
    private void loadRules() {
        Reflections reflection = new Reflections(INFERENCE_PACKAGE);
        Set<Class<?>> annotated = reflection.getTypesAnnotatedWith(InferenceRule.class);

        for(Class<?> clazz : annotated) {
            try {
                // For obvious reasons we assume the ruleName is set.
                String name = StringUtils.upperCase(clazz.getAnnotation(InferenceRule.class).ruleName());
                String type = StringUtils.upperCase(clazz.getAnnotation(InferenceRule.class).ruleType());
                final Rule newInstance = (Rule) clazz.getConstructor(InferenceType.class).newInstance(InferenceType.valueOf(type));
                // Just in case we need it, we store the rule type the class represents.
                this.inferenceRules.put(name, newInstance);
            } catch(InstantiationException ie) {
                logger.warn(String.format("Cannot Instantiate: [%s]", clazz.getName()));
            } catch(IllegalAccessException iae) {
                logger.warn(String.format("IllegalAccess: The class: [%s] could not be instantiated", clazz.getName()));
            } catch(NoSuchMethodException nsme) {
                logger.warn(String.format("We cannot find the correct instructor for: %s", clazz.getName()));
            } catch(InvocationTargetException ite) {
                logger.warn(String.format("We cannot invoke that dark magic (%s)", clazz.getName()));
            }
        }
    }
}
