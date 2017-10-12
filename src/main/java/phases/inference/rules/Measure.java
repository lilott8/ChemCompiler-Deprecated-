package phases.inference.rules;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference;
import substance.Property;

/**
 * @created: 10/11/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "measure", ruleType = "instruction")
public class Measure extends NodeAnalyzer {

    public static final Logger logger = LogManager.getLogger(Measure.class);
    private NodeAnalyzer detect = new Detect(Inference.InferenceType.INSTRUCTION);

    public Measure(Inference.InferenceType type) {
        super(type);
    }

    public Measure(Inference.InferenceType type, Class<? extends NodeAnalyzer> clazz) {
        super(type, clazz);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.detect.gatherAllConstraints(node);
    }

    @Override
    protected Rule gatherUseConstraints(String input) {
        return this.detect.gatherUseConstraints(input);
    }

    @Override
    protected Rule gatherDefConstraints(String input) {
        return this.detect.gatherDefConstraints(input);
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this.detect.gatherConstraints(property);
    }
}
