package ir.graph;


/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class HeatStatement extends BaseNop {

    public static final String INSTRUCTION = "HEAT";

    public HeatStatement(String name) {
        super(name);
    }
}
