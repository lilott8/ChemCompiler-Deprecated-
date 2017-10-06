package phases.inference.rules;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import compilation.datastructures.InstructionNode;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;
import typesystem.epa.ChemTypes;
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
public class Mix extends NodeAnalyzer {

    public Mix(InferenceType type) {
        super(type, Mix.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        //logger.trace(node);
        //logger.trace("Constraints: " + constraints);
        // This is the input to the instruction
        Set<ChemTypes> groups = new HashSet<>();
        List<ChemTypes> groupsList = new ArrayList<>();
        for(String in: node.getInputSymbols()) {
            // We don't know what this is.
            if (!this.constraints.containsKey(in)) {
                // TODO: converge int and chemtypes....
                //this.addConstraint(in, new GenericSMT(in))
                for (ChemTypes i : this.identifier.identifyCompoundForTypes(in)) {
                    this.addConstraint(in, i, ConstraintType.MIX);
                    groups.add(i);
                }
            } else {
                groups.addAll(this.constraints.get(in).getConstraints());
            }
            // logger.trace("Constraints: " + this.constraints.get(in));
            // logger.trace("-------------------------");
        }
        // logger.trace("Groups: " + groups);

        groupsList.addAll(groups);

        // The output of the instruction.
        for(String out : node.getOutputSymbols()) {
            this.addConstraints(out, groups, ConstraintType.MIX);
            combiner.combine(groupsList);
        }

        // Get the properties of the instruction if they exist
        for (Property prop : node.Instruction().getProperties()) {
            this.gatherConstraints(prop);
        }

        // logger.trace("=======================");
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraint(input, ChemTypes.MAT, ConstraintType.MIX);
        return this;
    }

    /**
     * This doesn't do anything because it is derived
     * from the gatherUseConstraints.
     * @param input
     * @return
     */
    @Override
    public Rule gatherDefConstraints(String input) {
        this.addConstraint(input, ChemTypes.MAT, ConstraintType.MIX);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(CONST, ChemTypes.REAL, ConstraintType.MIX);
        return this;
    }
}
