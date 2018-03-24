package typesystem.rules;

import compilation.datastructures.node.InstructionNode;
import typesystem.Inference.InferenceType;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
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

        //Formula instruction = new Formula(InstructionType.ASSIGN);

        // Output Symbol        Input Symbol
        // Allyl Ethyl Ether = C=CCOC1=CC=CC=C1
        /*
         * New workings here.
         */
        /*Term output = null;
        for (String s : node.getDef()) {
            output = new Term(s);
        }

        Term input = null;
        // This has to be input symbols.
        // There are no uses, these are the "constants".
        for (String s : node.getDispenseSymbols()) {
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
            logger.fatal("An assignment operation doesn't have a \"getDef()\"");
        }

        // The input is superfluous in an assign for type typesystem.
        // instruction.addInputVariable(input);
        instruction.addOutputVariable(output);

        // The input is superfluous in an assign for type typesystem.
        // addVariable(input);
        addVariable(output);

        for (Property p : node.getInstruction().getProperties()) {
            Variable prop = new Term(Rule.createHash(p.toString()), this.propertyTypes);
            prop.addTypingConstraint(REAL);
            instruction.addProperty(prop);
            addVariable(prop);
        }

        addInstruction(instruction);*/
        return this;
    }
}
