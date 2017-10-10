package phases.inference;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.reflections.Reflections;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.basicblock.BasicBlockEdge;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.InstructionNode;
import config.ConfigFactory;
import phases.Phase;
import phases.inference.rules.EdgeAnalyzer;
import phases.inference.rules.InferenceRule;
import phases.inference.rules.NodeAnalyzer;
import phases.inference.satsolver.SatSolver;
import phases.inference.satsolver.constraints.Constraint;
import phases.inference.satsolver.strategies.Z3Strategy;
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

    // This maps each instruction/term to the constraints that it has.
    private Map<String, Constraint> constraints = new HashMap<>();

    // This is for human readability and testing only.  This will be removed for production.
    private Map<Tuple<String, String>, Set<ChemTypes>> testingConstraints = new HashMap<Tuple<String, String>, Set<ChemTypes>>();

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
                if(node.Instruction() != null) {
                    // This will give us the typing of all the constraints in the instruction.
                    this.addConstraints(this.inferConstraints(StringUtils.upperCase(node.Instruction().getClassification()), node));
                }
                // logger.info(node.Instruction());
            }
        }

        // Iterate the edges, we need the branch conditions to infer...
        for(BasicBlockEdge edge : this.controlFlowGraph.getBasicBlockEdges()) {
            this.addConstraints(this.inferConstraints(StringUtils.upperCase(edge.getClassification()), edge));
        }

        if (ConfigFactory.getConfig().isDebug()) {
            logger.trace(this.constraints);
        }

        return this.solver.setSatSolver(new Z3Strategy()).solveConstraints(constraints);
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
    public Map<String, Constraint> inferConstraints(String name, InstructionNode instruction) {
        if(this.basicBlockAnalyzers.containsKey(name)) {
            NodeAnalyzer rule = this.basicBlockAnalyzers.get(name);
            return rule.gatherAllConstraints(instruction).getConstraints();
            // return the constraints from the rule
            //return rule.getConstraints();
            //return this.inferenceRules.get(name).gatherConstraints(instruction).getConstraints();
        }
        logger.warn("Node Analysis: We don't have a rule for: " + name);
        // return an empty array list for ease.
        return new HashMap<>();
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
    public Map<String, Constraint> inferConstraints(String name, BasicBlockEdge edge) {
        if (this.edgeAnalyzers.containsKey(name)) {
            EdgeAnalyzer rule = this.edgeAnalyzers.get(name);
            return rule.gatherConstraints(edge).getConstraints();
        }
        if (!StringUtils.equalsIgnoreCase(name, "unknown")) {
            logger.warn("Edge Analysis: We don't have a rule for: " + name);
        }

        return new HashMap<>();
    }

    /**
     * Allows adding of constraints to terms/instructions
     * @param constraints
     *   HashSet of constraints
     */
    private void addConstraints(Map<String, Constraint> constraints) {
        // If the constraints are empty, don't do anything
        if(constraints == null || constraints.isEmpty()) {
            return;
        }

        // Otherwise add all constraints to the appropriate key.
        for (Map.Entry<String, Constraint> entry : constraints.entrySet()) {
            if (!this.constraints.containsKey(entry.getKey())) {
                this.constraints.put(entry.getKey(), entry.getValue());
            }
            this.constraints.put(entry.getKey(), entry.getValue());
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
}
