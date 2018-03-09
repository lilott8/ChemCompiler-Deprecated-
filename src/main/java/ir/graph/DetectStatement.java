package ir.graph;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class DetectStatement extends BaseStatement {

    public static final String INSTRUCTION = "DETECT";

    public DetectStatement() {
        super(INSTRUCTION);
    }
}
