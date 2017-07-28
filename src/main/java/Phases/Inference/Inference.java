package Phases.Inference;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import Phases.Phase;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * Because it is too cumbersome to implement a `Visitor` pattern here,
 *  we just rely on the base API that exists...
 */
public class Inference implements Phase {

    public static final Logger logger = LogManager.getLogger(Inference.class);

    // This maps each instruction/term to the constraints that it has
    private Map<String, Set> constraints = new HashMap<String, Set>();
    private CFG controlFlowGraph;

    public Inference() {

    }

    public Inference addCFG(CFG controlFlowGraph) {
        this.controlFlowGraph = controlFlowGraph;
        return this;
    }

    public Inference runInference() {
        for(Map.Entry<Integer, BasicBlock> block : this.controlFlowGraph.getBasicBlocks().entrySet()) {
            logger.info(block);
        }
        return this;
    }

    public void runPhase(CFG controlFlowGraph) {
        this.controlFlowGraph = controlFlowGraph;
        this.runInference();
    }

    public Map<String, Set> getConstraints() {
        return this.constraints;
    }

    public void addConstraint(String variable, String type) {
        if (!this.constraints.containsKey(variable)) {
            this.constraints.put(variable, new HashSet());
        }
        this.constraints.get(variable).add(type);
    }
}
