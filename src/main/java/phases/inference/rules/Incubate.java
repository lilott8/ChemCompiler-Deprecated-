package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import javafx.scene.Node;
import phases.inference.Inference;
import substance.Property;

/**
 * @created: 10/11/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "incubate", ruleType = "instruction")
public class Incubate extends NodeAnalyzer {

    private NodeAnalyzer heat;

    public Incubate(Inference.InferenceType type) {
        super(type, Incubate.class);
        this.heat = new Heat(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return this.heat.gatherAllConstraints(node);
    }

    @Override
    protected Rule gatherUseConstraints(String input) {
        return this.heat.gatherUseConstraints(input);
    }

    @Override
    protected Rule gatherDefConstraints(String input) {
        return this.heat.gatherDefConstraints(input);
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this.heat.gatherConstraints(property);
    }
}
