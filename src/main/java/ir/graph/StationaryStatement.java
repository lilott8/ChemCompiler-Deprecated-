package ir.graph;

/**
 * @created: 3/6/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class StationaryStatement extends BaseNop {

    public static final String INSTRUCTION = "STATIONARY";

    public StationaryStatement() {
        super(INSTRUCTION);
    }

}
