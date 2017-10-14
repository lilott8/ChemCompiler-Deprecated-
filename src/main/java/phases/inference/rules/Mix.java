package phases.inference.rules;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import compilation.datastructures.InstructionNode;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;
import typesystem.epa.ChemTypes;
import phases.inference.Inference.InferenceType;
import substance.Property;
import typesystem.epa.EpaManager;

import static typesystem.epa.ChemTypes.REAL;

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
            // We don't know what this is -- this case should never fire.
            if (!this.constraints.containsKey(in)) {
                logger.error("We shouldn't be identifying [" + in +  "] on input.");
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

        /*
         * This begins the new inference gathering.
         */
        Instruction instruction = new Instruction(node.ID(), Mix.class.getName());
        Variable output;
        if (node.getOutputSymbols().size() > 0) {
            output = new Term(node.getOutputSymbols().get(0));
        } else {
            output = new Term(node.getInputSymbols().get(node.getInputSymbols().size()-1));
        }

        for (String in : node.getInputSymbols()) {
            Variable input = new Term(in);
            if (variables.containsKey(input.getVarName())) {
                input.addTypingConstraints(variables.get(input.getVarName()).getTypingConstraints());
            } else {
                logger.warn(input.getVarName() + " has no previous declarations...");
            }
            instruction.addInputTerm(input);
            // We can use the input for the naive approach to the output
            output.addTypingConstraints(input.getTypingConstraints());
        }
        // Reference the lookup table
        output.addTypingConstraints(EpaManager.INSTANCE.lookUp(output.getTypingConstraints()));
        // Finally add the types to the output
        instruction.addOutputTerm(output);

        addVariable(output);
        for (Variable v : instruction.getInput()) {
            addVariable(v);
        }

        // Get the properties of the instruction if they exist
        for (Property p : node.Instruction().getProperties()) {
            Variable prop = new Term(Rule.createHash(p.toString()));
            prop.addTypingConstraint(REAL);
            instruction.addInputTerm(prop);
            addVariable(prop);
        }

        addInstruction(instruction);
        // logger.trace("=======================");
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        this.addConstraints(input, new HashSet<>(), ConstraintType.MIX);
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
        this.addConstraints(input, new HashSet<>(), ConstraintType.MIX);
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        addVariable(new Term(Rule.createHash(property.toString())).addTypingConstraint(REAL));
        this.addConstraint(Rule.createHash(property.toString()), REAL, ConstraintType.NUMBER);
        return this;
    }
}
