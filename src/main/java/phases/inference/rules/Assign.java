package phases.inference.rules;

import compilation.datastructures.InstructionNode;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import typesystem.epa.ChemTypes;
import phases.inference.Inference.InferenceType;
import substance.Property;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;

import static typesystem.epa.ChemTypes.NAT;
import static typesystem.epa.ChemTypes.REAL;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 */

@InferenceRule(ruleName = "assign", ruleType = "term")
public class Assign extends NodeAnalyzer {

    public Assign(InferenceType type) {
        super(type, Assign.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        if (this.config.isDebug()) {
             //logger.trace(node);
             //logger.trace("Input: " + node.getInputSymbols());
             //logger.trace("Output: " + node.getOutputSymbols());
        }

        // Output Symbol        Input Symbol
        // Allyl Ethyl Ether = C=CCOC1=CC=CC=C1
        /*
         * New workings here.
         */
        Term output = null;
        for (String s : node.get_def()) {
            output = new Term(s);
        }

        Term input = null;
        // This has to be input symbols.
        // There are no uses, these are the "constants".
        for (String s : node.getInputSymbols()) {
            input = new Term(s);
        }

        try {
            // See if this is a number.
            if (isNumeric(output.getVarName())) {
                if (isRealNumber(output.getVarName())) {
                    output.addTypingConstraint(REAL);
                } else {
                    output.addTypingConstraint(NAT);
                }
            } else {
                output.addTypingConstraints(this.identifier.identifyCompoundForTypes(input.name));
            }
        } catch(NullPointerException e) {
            logger.fatal("An assignment operation doesn't have a \"get_def()\"");
        }

        Instruction instruction = new Instruction(node.ID(), Assign.class.getName());
        // The input is superfluous in an assign for type inference.
        // instruction.addInputVariable(input);
        instruction.addOutputVariable(output);

        // The input is superfluous in an assign for type inference.
        // addVariable(input);
        addVariable(output);
        addInstruction(instruction);

        for (Property p : node.Instruction().getProperties()) {
            Variable prop = new Term(Rule.createHash(p.toString()));
            prop.addTypingConstraint(REAL);
            instruction.addInputVariable(prop);
            addVariable(prop);
        }
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        if (isNumeric(input)) {
            this.addConstraint(Rule.createHash(input), isRealNumber(input) ? ChemTypes.REAL : ChemTypes.NAT, ConstraintType.NUMBER);
        } else {
            this.addConstraints(input, this.identifier.identifyCompoundForTypes(input), ConstraintType.ASSIGN);
        }
        return this;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return this;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        addVariable(new Term(Rule.createHash(property.toString())).addTypingConstraint(ChemTypes.REAL));
        this.addConstraint(Rule.createHash(property.toString()), ChemTypes.REAL, ConstraintType.NUMBER);
        return this;
    }
}
