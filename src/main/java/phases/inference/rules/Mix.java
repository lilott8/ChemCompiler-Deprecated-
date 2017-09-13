package phases.inference.rules;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.Set;

import compilation.datastructures.InstructionNode;
import phases.inference.ChemTypes;
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
        for(String in: node.getInputSymbols()) {
            if (!this.constraints.containsKey(in)) {
                // TODO: converge int and chemtypes....
                //for (ChemTypes t : this.identifier.identifyCompound(in).getReactiveGroups()) {
                //    this.addConstraint(in, t);
                //    groups.add(t);
                //}
            } else {
                groups.addAll(this.constraints.get(in).getConstraints());
            }
        }
        //logger.trace("Groups: " + groups);

        // Simulate the mix for the types.
        Set<ChemTypes> unions = new HashSet<>();
        unions = groups;
        //for(int x = 1; x < groups.size(); x++) {
        //    for (int y = x; y < groups.size(); y++) {
        //        unions.addAll(this.identifier.getReaction(x, y));
        //    }
        //}

        // The output of the instruction.
        for(String out : node.getOutputSymbols()) {
            this.addConstraints(out, unions);
        }

        // Get the properties of the instruction if they exist
        for (Property prop : node.Instruction().getProperties()) {
            this.gatherConstraints(prop);
        }

        //logger.trace("=======================");
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraint(input, ChemTypes.MAT);
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
        this.addConstraint(input, ChemTypes.MAT);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        this.addConstraint(CONST, ChemTypes.REAL);
        return this;
    }
}
