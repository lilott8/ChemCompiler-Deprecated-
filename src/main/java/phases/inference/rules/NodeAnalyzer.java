package phases.inference.rules;


import java.util.List;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import substance.Property;
import typesystem.combinator.Combiner;
import typesystem.combinator.CombinerFactory;
import typesystem.identification.Identifier;
import typesystem.identification.IdentifierFactory;

import static typesystem.epa.ChemTypes.REAL;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class NodeAnalyzer extends Rule {

    protected Identifier identifier;
    protected Combiner combiner;

    protected NodeAnalyzer(InferenceType type) {
        super(type);
    }

    protected NodeAnalyzer(InferenceType type, Class<? extends NodeAnalyzer> clazz) {
        super(type, clazz);
    }

    {
        this.identifier = IdentifierFactory.getIdentifier();
        this.combiner = CombinerFactory.getCombiner();
    }

    public abstract Rule gatherAllConstraints(InstructionNode node);
    protected abstract Rule gatherUseConstraints(String input);
    protected abstract Rule gatherDefConstraints(String input);
    public abstract Rule gatherConstraints(Property property);

    protected Instruction gatherProperties(Instruction instruction, List<Property> properties) {
        for (Property p : properties) {
            Variable prop = new Term(Rule.createHash(p.toString()));
            prop.addTypingConstraint(REAL);
            instruction.addInputVariable(prop);
            addVariable(prop);
        }
        return instruction;
    }

    protected Rule gatherConstraints(InstructionNode node) {
        /*
         * Temp = Mix x with y for n
         *  ^def_use  |      |     |
         *         get_use   |     |
         *                get_use  |
         *                      property
         */
        // These are the defs on instruction
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

        /*
        logger.debug("Id: " + instruction.ID());
        logger.debug("Classification: " + instruction.Instruction().getClassification());
        logger.debug("Input Symbols: " + instruction.getInputSymbols());
        logger.debug("Properties: " + instruction.Instruction().getProperties());
        logger.debug("Use: " + instruction.get_use());
        logger.debug("Def: " + instruction.get_def());
        logger.debug("Output Symbols: " + instruction.getOutputSymbols());
        logger.debug("toString(): " + instruction.toString());
        logger.warn("=================================");
        */
        return this;
    }
}
