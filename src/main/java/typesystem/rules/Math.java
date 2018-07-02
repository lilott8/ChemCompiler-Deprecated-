package typesystem.rules;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import compilation.datastructures.node.InstructionNode;
import shared.variable.NamedVariable;
import shared.variable.ManifestVariable;
import shared.variable.Variable;
import typesystem.Inference.InferenceType;
import typesystem.elements.Formula;

import static chemical.epa.ChemTypes.NAT;
import static chemical.epa.ChemTypes.REAL;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "math", ruleType = "term")
public class Math extends NodeAnalyzer {

    public Math(InferenceType type) {
        super(type, Math.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        Formula instruction = new Formula(InstructionType.MATH);

        Set<ChemTypes> outputTypes = new HashSet<>();
        // There can be only one input variable.
        Variable input = null;
        for (String s : node.getUse()) {
            input = new ManifestVariable(s);
            Set<ChemTypes> set = new HashSet<>();
            set.addAll(this.getTypingConstraints(input));
            if (set.isEmpty()) {
                input.addTypingConstraint(REAL);
                input.addTypingConstraint(NAT);
            } else {
                input.addTypingConstraints(set);
            }
            outputTypes.addAll(input.getTypingConstraints());
            instruction.addInputVariable(input);
            addVariable(input);
        }

        // There can be only one output variable.
        Variable output = null;
        for (String s : node.getDef()) {
            output = new NamedVariable(s);
            output.addTypingConstraint(REAL);
            output.addTypingConstraint(NAT);
            output.addTypingConstraints(outputTypes);
            instruction.addOutputVariable(output);
            addVariable(output);
        }

        addInstruction(instruction);
        return this;
    }
}
