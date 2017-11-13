package phases.inference;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.reflections.Reflections;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.basicblock.BasicBlockEdge;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.node.InstructionNode;
import phases.Phase;
import phases.inference.elements.Instruction;
import phases.inference.elements.Variable;
import phases.inference.rules.EdgeAnalyzer;
import phases.inference.rules.InferenceRule;
import phases.inference.rules.NodeAnalyzer;
import phases.inference.satsolver.SatSolver;
import phases.inference.satsolver.strategies.Z3Strategy;
import shared.Delete;
import shared.Tuple;
import typesystem.epa.ChemTypes;

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
        TERM, INSTRUCTION, BRANCH
    }

    public final String NODE_ANALYSIS = "NODE";
    public final String EDGE_ANALYSIS = "EDGE";

    // Logging mechanism.
    public static final Logger logger = LogManager.getLogger(Inference.class);

    // Package for where to look for annotated rules.
    public static final String INFERENCE_PACKAGE = "phases.inference.rules";

    /**
     * We have two because the differences between blocks
     * and edges are stark.  So this enforces guarantees that
     * each analyzer will do exactly what it's supposed to,
     * and make troubleshooting easier.
     */
    private final Map<String, NodeAnalyzer> basicBlockAnalyzers = new HashMap<>();
    private final Map<String, EdgeAnalyzer> edgeAnalyzers = new HashMap<>();

    // Contains the typing constraints for instructions.
    private Map<Integer, Instruction> instructions = new HashMap<>();
    // Contains the typing constraints for all terms.
    private Map<String, Variable> variables = new HashMap<>();

    // This is for human readability and testing only.  This will be removed for production.
    private Map<Tuple<String, String>, Set<ChemTypes>> testingConstraints = new HashMap<Tuple<String, String>, Set<ChemTypes>>();

    // How are we going to solve this type inference problem?
    private SatSolver solver = new SatSolver();

    // Control flow graph needed to infer types from.
    private CFG controlFlowGraph;

    // Default Constructor
    public Inference() {
        this.loadRules();
    }

    /**
     * Run the inference phase of the compilation process.
     * @param controlFlowGraph
     */
    public boolean runPhase(CFG controlFlowGraph) {
        this.controlFlowGraph = controlFlowGraph;

        // Iterate the CFG.
        for(Map.Entry<Integer, BasicBlock> block : this.controlFlowGraph.getBasicBlocks().entrySet()) {
            // Iterate the instructions.
            for(InstructionNode node : block.getValue().getInstructions()) {
                // If we have an instruction, see what we can infer.
                if(node.getInstruction() != null) {
                    // This will give us the typing of all the constraints in the instruction.
                    this.inferConstraints(StringUtils.upperCase(node.getInstruction().getClassification()), node);
                }
            }
        }

        // Iterate the edges, we need the branch conditions to infer...
        for(BasicBlockEdge edge : this.controlFlowGraph.getBasicBlockEdges()) {
            this.inferConstraints(StringUtils.upperCase(edge.getClassification()), edge);
        }

        printStatistics();

        // logger.info(this.instructions);
        // logger.debug(this.variables);
        return this.solver.setSatSolver(new Z3Strategy()).solveConstraints(this.instructions, this.variables);
    }

    /**
     * Infer the constraint from the instruction.
     * @param name
     *   Name of the instruction.
     * @param instruction
     *   getInstruction to be inferred.
     * @return
     *   A mapping of id to what was inferred.
     */
    public void inferConstraints(String name, InstructionNode instruction) {
        if(this.basicBlockAnalyzers.containsKey(name)) {
            NodeAnalyzer rule = this.basicBlockAnalyzers.get(name);
            rule = (NodeAnalyzer) rule.gatherAllConstraints(instruction);
            this.addInstructions(rule.getInstructions());
            this.addTerms(rule.getVariables());
        } else {
            logger.warn("Node Analysis: We don't have a rule for: " + name);
        }
        // return an empty array list for ease.
    }

    /**
     * Infer constraints from edges.
     * This handles if/elseif/else and repeats
     *
     * @param name
     *   Name of the instruction.
     * @param edge
     *   Edge between basic blocks.
     * @return
     *   A mapping of id to what was inferred.
     */
    public void inferConstraints(String name, BasicBlockEdge edge) {
        if (this.edgeAnalyzers.containsKey(name)) {
            EdgeAnalyzer rule = this.edgeAnalyzers.get(name);
            rule = (EdgeAnalyzer) rule.gatherConstraints(edge);
            this.addInstructions(rule.getInstructions());
            this.addTerms(rule.getVariables());
        }
        if (!this.edgeAnalyzers.containsKey(name) && !StringUtils.equalsIgnoreCase(name, "unknown")) {
            logger.warn("Edge Analysis: We don't have a rule for: " + name);
        }
    }

    private void addInstructions(Map<Integer, Instruction> i) {
        this.instructions.putAll(i);
    }

    private void addTerms(Map<String, Variable> t) {
        for (Map.Entry<String, Variable> entry : t.entrySet()) {
            if (this.variables.containsKey(entry.getKey())) {
                // pass, for now
            } else {
                this.variables.put(entry.getKey(), entry.getValue());
            }
        }
    }

    /**
     * @return
     *   String representation.
     */
    public String toString() {
        return super.toString() + this.instructions;
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
                String analyze = StringUtils.lowerCase(clazz.getAnnotation(InferenceRule.class).analyze());
                if (StringUtils.equalsIgnoreCase(analyze, NODE_ANALYSIS)) {
                    final NodeAnalyzer newInstance = (NodeAnalyzer) clazz.getConstructor(InferenceType.class).newInstance(InferenceType.valueOf(type));
                    this.basicBlockAnalyzers.put(name, newInstance);
                } else {
                    final EdgeAnalyzer newInstance = (EdgeAnalyzer) clazz.getConstructor(InferenceType.class).newInstance(InferenceType.valueOf(type));
                    this.edgeAnalyzers.put(name, newInstance);
                }
                // Just in case we need it, we store the rule type the class represents.
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

    private void printStatistics() {
        double average = 0;
        int total = 0;
        int max = 0;
        int min = 100000;
        List<Integer> medianContainer = new ArrayList<>();

        for (Map.Entry<String, Variable> varEntry : this.variables.entrySet()) {
            medianContainer.add(varEntry.getValue().getTypingConstraints().size());
            total += varEntry.getValue().getTypingConstraints().size();
            if (varEntry.getValue().getTypingConstraints().size() < min) {
                min = varEntry.getValue().getTypingConstraints().size();
            }
            if (varEntry.getValue().getTypingConstraints().size() > max) {
                max = varEntry.getValue().getTypingConstraints().size();
            }
        }

        average = total / ((double) medianContainer.size());

        Delete.writer.write(String.format("%d|%d|%d|%d|%.02f", min, max, total, findMedian(medianContainer), average));
    }

    private int findMedian(List<Integer> nums) {
        Collections.sort(nums);
        int middle = Math.floorDiv(nums.size(), 2);
        return nums.get(middle);
    }
}
