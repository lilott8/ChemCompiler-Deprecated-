package phases.inference.rules;

import phases.inference.satsolver.Solver;

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

    public Solver gatherConstraints(InstructionNode node, Solver solver) {

        for (String out : node.get_def()) {
            this.addConstraint(out, "Mat");
        }

        for (String in : node.get_use()) {
            this.addConstraint(in, "Mat");
        }

        for (Property prop : node.Instruction().getProperties()) {
            this.addConstraint("constant", "Real");
        }
        return solver;
    }

    @Override
    public Solver gatherUseConstraints(String input, Solver solver) {
        this.addConstraint(input, MAT);
        return solver;
    }

    @Override
    public Solver gatherDefConstraints(String input, Solver solver) {
        this.addConstraint(input, MAT);
        return solver;
    }

    @Override
    public Solver gatherConstraints(Property property, Solver solver) {
        this.addConstraint(CONST, REAL);
        return solver;
    }
}
