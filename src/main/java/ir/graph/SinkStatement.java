package ir.graph;

/**
 * @created: 3/7/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SinkStatement extends BaseNop {

    public static final String INSTRUCTION = "SINK";

    public SinkStatement() {
        super(INSTRUCTION);
    }
}
