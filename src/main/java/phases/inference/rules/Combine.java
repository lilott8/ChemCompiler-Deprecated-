package phases.inference.rules;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import CompilerDataStructures.InstructionNode;
import phases.inference.Inference;
import substance.Property;

/**
 * @created: 8/10/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * This is a synonym for mix, thus we just wrap it as such.
 */
@InferenceRule(ruleName = "combine", ruleType = "instruction")
public class Combine extends Rule {

    public static final Logger logger = LogManager.getLogger(Mix.class);
    private Rule mix = new Mix(Inference.InferenceType.INSTRUCTION);

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        return mix.gatherAllConstraints(node);
    }

    public Combine(Inference.InferenceType type) {
        super(type);
    }
    @Override
    public Rule gatherUseConstraints(String input) {
        return mix.gatherUseConstraints(input);
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return this.mix.gatherDefConstraints(input);
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this.mix.gatherConstraints(property);
    }
}
