package ir.graph;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SplitStatement extends BaseStatement {

    public static final String INSTRUCTION = "SPLIT";

    public SplitStatement() {
        super(INSTRUCTION);
    }
}
