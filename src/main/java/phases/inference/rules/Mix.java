package phases.inference.rules;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import CompilerDataStructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * Mat = mix Mat with Mat ... for Real
 */
@InferenceRule(ruleName = "mix", ruleType = "instruction")
public class Mix extends Rule {

    public static final Logger logger = LogManager.getLogger(Mix.class);

    public Mix(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        for(String out : node.get_def()) {
            this.gatherDefConstraints(out);
        }

        // This is the input to the instruction
        for(String in: node.get_use()) {
            this.gatherUseConstraints(in);
        }

        // Get the properties of the instruction if they exist
        for (Property prop : node.Instruction().getProperties()) {
            this.gatherConstraints(prop);
        }
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraint(input, MAT);
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, MAT);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(CONST, REAL);
        return this;
    }
}
