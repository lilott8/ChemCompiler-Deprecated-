package typesystem.rules;

import compilation.datastructures.node.InstructionNode;
import typesystem.Inference;

/**
 * @created: 10/11/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "measure", ruleType = "instruction")
public class Measure extends NodeAnalyzer {

    //public static final Logger logger = LogManager.getLogger(Measure.class);
    private NodeAnalyzer detect = new Detect(Inference.InferenceType.INSTRUCTION);

    public Measure(Inference.InferenceType type) {
        super(type, Measure.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.detect.gatherAllConstraints(node);
    }
}
