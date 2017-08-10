package Phases.Inference.Rules;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import CompilerDataStructures.InstructionNode;
import Phases.Inference.Inference.InferenceType;
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
    public Rule gatherConstraints(InstructionNode node) {
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
    public Rule gatherUseConstraints(String input) {
        if (this.isNumeric(input)) {
            this.addConstraint(input, NAT);
            this.addConstraint(input, REAL);
        } else {
            this.addConstraint(input, MAT);
        }
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return null;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return this;
    }
}
