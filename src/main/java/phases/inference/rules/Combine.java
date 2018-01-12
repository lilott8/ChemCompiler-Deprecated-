package phases.inference.rules;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import compilation.datastructures.node.InstructionNode;
import phases.inference.Inference;

/**
 * @created: 8/10/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * This is a synonym for mix, thus we just wrap it as such.
 */
@InferenceRule(ruleName = "combine", ruleType = "instruction")
public class Combine extends NodeAnalyzer {

    public static final Logger logger = LogManager.getLogger(Mix.class);
    private NodeAnalyzer mix = new Mix(Inference.InferenceType.INSTRUCTION);

    public Combine(Inference.InferenceType type) {
        super(type, Combine.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.mix.gatherAllConstraints(node);
    }
}
