package ir.graph;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class LoopStatement extends BaseConditional {

    public static final String INSTRUCTION = "LOOP";

    public LoopStatement(String name, String condition) {
        super(name, condition);
    }
}
