package phases.inference;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;

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
import CompilerDataStructures.BasicBlock.BasicBlockEdge;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.InstructionNode;
import phases.Phase;
import phases.inference.rules.InferenceRule;
import phases.inference.rules.Rule;
import phases.inference.satsolver.SatSolver;
import phases.inference.satsolver.strategies.Z3Strategy;
import shared.Tuple;

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
    public static final String INFERENCE_PACKAGE = "phases.inference.rules";

    // This maps the rule name the corresponding rule.
    private final Map<String, Rule> inferenceRules = new HashMap<>();
    //private final Map<String, Class<? extends Rule>> inferenceRules = new HashMap<>();

    // This maps each instruction/term to the constraints that it has.
    private Map<String, Set<String>> constraints = new HashMap<String, Set<String>>();

    // This is for human readability and testing only.  This will be removed for production.
    private Map<Tuple<String, String>, Set<String>> testingConstraints = new HashMap<Tuple<String, String>, Set<String>>();

    private SatSolver solver = new SatSolver();
    // Control flow graph needed to infer types from.
    private CFG controlFlowGraph;

    // Default Constructor
    public Inference() {
        this.loadRules();
    }

    private void test() {
        logger.trace("We are debugging things, remove the inference.test method.");

        Context context = new Context();

        Symbol fname = context.mkSymbol("f");
        Symbol x = context.mkSymbol("x");
        Symbol y = context.mkSymbol("y");

        Sort bs = context.mkBoolSort();

        Sort[] domain = {bs, bs};
        // Take in two booleans, return a boolean
        FuncDecl f = context.mkFuncDecl(fname, domain, bs);
        // This is an application of a function.
        Expr fapp = context.mkApp(f, context.mkConst(x, bs), context.mkConst(y, bs));

        Expr[] fargs2 = {context.mkFreshConst("cp", bs)};
        Sort[] domain2 = {bs};
        // Create a new function and apply it
        Expr fapp2 = context.mkApp(context.mkFreshFuncDecl("fp", domain2, bs), fargs2);

        BoolExpr trivial_eq = context.mkEq(fapp, fapp);
        BoolExpr nontrivial_eq = context.mkEq(fapp, fapp2);

        Goal g = context.mkGoal(true, false, false);
        g.add(trivial_eq);
        g.add(nontrivial_eq);
        logger.warn("Goal: " + g);
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
                    this.addConstraints(this.inferConstraints(StringUtils.upperCase(node.Instruction().getClassification()), node));
                }
                // logger.info(node.Instruction());
            }
        }

        // Iterate the edges, we need the branch conditions to infer...
        for(BasicBlockEdge edge : this.controlFlowGraph.getBasicBlockEdges()) {
            this.addConstraints(this.inferConstraints("edge", edge));
        }

        this.solver.setSatSolver(new Z3Strategy()).solveConstraints(constraints);
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
    public Map<String, Set<String>> inferConstraints(String name, InstructionNode instruction) {
        if(this.inferenceRules.containsKey(name)) {
            Rule rule = this.inferenceRules.get(name);
            return rule.gatherAllConstraints(instruction).getConstraints();
            // return the constraints from the rule
            //return rule.getConstraints();
            //return this.inferenceRules.get(name).gatherConstraints(instruction).getConstraints();
        }
        logger.warn("We don't have a rule for: " + name);
        // return an empty array list for ease.
        return new HashMap<String, Set<String>>();
    }

    /**
     * Infer constraints from edges.
     *
     * @param name
     *   Name of the instruction.
     * @param edge
     *   Edge between basic blocks.
     * @return
     *   A mapping of id to what was inferred.
     */
    public Map<String, Set<String>> inferConstraints(String name, BasicBlockEdge edge) {
        Map<String, Set<String>> results = new HashMap<>();

        // Split the condition into a string, get the operands and attempt to infer.
        for(String s : StringUtils.split(edge.getCondition())) {
            // we don't have the
            if (!Rule.operands.contains(s)) {

                // We cannot define a variable here, so we can safely look
                // into the global constraints table.
                if (this.constraints.containsKey(s)) {
                    // create the set if we don't have it yet.
                    if (!results.containsKey(s)) {
                        results.put(s, new HashSet<>());
                    }
                    results.get(s).add(Rule.NAT);
                }

                if (Rule.isNumeric(s)) {
                    if (!results.containsKey(s)) {
                        results.put(s, new HashSet<>());
                    }
                    results.get(s).add(Rule.REAL);
                    results.get(s).add(Rule.NAT);
                }
            } else {
                results.put("if", new HashSet<>());
                results.get("if").add(Rule.NAT);
            }
            //logger.info(s);
        }
        return results;
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
