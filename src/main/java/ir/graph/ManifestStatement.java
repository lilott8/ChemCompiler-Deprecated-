package ir.graph;

/**
 * @created: 3/6/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ManifestStatement extends BaseNop {

    public static final String INSTRUCTION = "MANIFEST";

    public ManifestStatement(String name) {
        super(name);
    }
}
