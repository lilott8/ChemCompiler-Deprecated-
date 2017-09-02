package phases.inference.rules;


import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import substance.Property;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class NodeAnalyzer extends Rule {

    public NodeAnalyzer(InferenceType type) {
        super(type);
    }

    public abstract Rule gatherAllConstraints(InstructionNode node);
    public abstract Rule gatherUseConstraints(String input);
    public abstract Rule gatherDefConstraints(String input);
    public abstract Rule gatherConstraints(Property property);

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
