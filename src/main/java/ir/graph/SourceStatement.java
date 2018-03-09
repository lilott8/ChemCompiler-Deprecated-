package ir.graph;

/**
 * @created: 3/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SourceStatement extends BaseNop implements Nop {

    public static final String INSTRUCTION = "SOURCE";

    public SourceStatement() {
        super(INSTRUCTION);
    }
}
