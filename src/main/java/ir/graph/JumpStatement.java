package ir.graph;

/**
 * @created: 3/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class JumpStatement extends BaseStatement {

    public final static String INSTRUCTION = "JUMP";

    protected JumpStatement(String name) {
        super(name);
    }
}
