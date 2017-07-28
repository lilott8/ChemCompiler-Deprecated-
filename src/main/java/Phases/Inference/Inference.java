package Phases.Inference;

import com.google.common.reflect.Reflection;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.reflections.Reflections;

import java.io.File;
import java.lang.reflect.Field;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.InstructionNode;
import Phases.Inference.Rules.InferenceRule;
import Phases.Phase;
import Shared.Tuple;
import executable.instructions.Instruction;

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

    public static final Logger logger = LogManager.getLogger(Inference.class);

    public static final String INFERENCE_PACKAGE = "Phases.Inference.Rules";

    private final Map<String, Callback> inferenceRules = new HashMap<String, Callback>();

    // This maps each instruction/term to the constraints that it has
    private Map<Tuple<Long, String>, Set<String>> constraints = new HashMap<Tuple<Long, String>, Set<String>>();
    private CFG controlFlowGraph;

    public Inference() {
        this.loadRules();
        for(Map.Entry<String, Callback> entry : this.inferenceRules.entrySet()) {
            logger.info(entry.getKey());
        }
    }

    public void runPhase(CFG controlFlowGraph) {
        this.controlFlowGraph = controlFlowGraph;
        for(Map.Entry<Integer, BasicBlock> block : this.controlFlowGraph.getBasicBlocks().entrySet()) {
            for(InstructionNode node : block.getValue().getInstructions()) {
                if(node.Instruction() != null) {
                    Tuple<Long, String> tuple = new Tuple<Long, String>(node.Instruction().getId(), node.Instruction().getName());
                    this.addConstraint(tuple, this.inferConstraint(tuple.getRight(), node));
                }
                // logger.info(node.Instruction());
            }
        }

        logger.info(this.toString());
    }

    public Set<String> inferConstraint(String name, InstructionNode instruction) {
        if(this.inferenceRules.containsKey(name)) {
            return this.inferenceRules.get(name).callback(instruction);
        }
        logger.warn("We don't have a callback for: " + name);
        // return an empty array list for ease.
        return new HashSet<String>();
    }

    /**
     * Allows adding of constraints to terms/instructions
     * @param tuple
     * @param inferred
     */
    private void addConstraint(Tuple<Long, String> tuple, Set<String> inferred) {
        if (!this.constraints.containsKey(tuple)) {
            this.constraints.put(tuple, new HashSet<String>());
        }
        if(inferred != null) {
            this.constraints.get(tuple).addAll(inferred);
        }
    }

    public String toString() {
        return this.constraints.toString();
    }

    private void loadRules() {
        Reflections reflection = new Reflections(INFERENCE_PACKAGE);
        Set<Class<?>> annotated = reflection.getTypesAnnotatedWith(InferenceRule.class);

        for(Class<?> clazz : annotated) {
            try {
                // For obvious reasons we assume the ruleName is set.
                String name = StringUtils.capitalize(clazz.getAnnotation(InferenceRule.class).ruleName());
                final Callback newInstance = (Callback) clazz.newInstance();
                this.inferenceRules.put(name, newInstance);
            } catch(InstantiationException ie) {
                logger.warn(String.format("Cannot Instatiate: [%s]", clazz.getName()));
            } catch(IllegalAccessException iae) {
                logger.warn(String.format("IllegalAccess: The class: [%s] could not be instantiated", clazz.getName()));
            }
        }
    }
}
