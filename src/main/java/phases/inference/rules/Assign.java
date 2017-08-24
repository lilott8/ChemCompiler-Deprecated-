package phases.inference.rules;

import phases.inference.satsolver.Solver;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import CompilerDataStructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 */

@InferenceRule(ruleName = "assign", ruleType = "term")
public class Assign extends Rule {

    public Assign(InferenceType type) {
        super(type);
    }

    @Override
    public Solver gatherConstraints(InstructionNode node, Solver solver) {
        return null;
    }

    public InferenceType getType() {
        return this.type;
    }

    public Map<String, Set<String>> callback(InstructionNode node) {
        Map<String, Set<String>> results = new HashMap<String, Set<String>>();

        return results;
    }

    @Override
    public Solver gatherUseConstraints(String input, Solver solver) {
        if (this.isNumeric(input)) {
            this.addConstraint(input, NAT);
            this.addConstraint(input, REAL);
        } else {
            this.addConstraint(input, MAT);
        }
        return solver;
    }

    @Override
    public Solver gatherDefConstraints(String input, Solver solver) {
        return solver;
    }

    @Override
    public Solver gatherConstraints(Property property, Solver solver) {
        return solver;
    }
}
