package ir.graph;

/**
 * @created: 3/6/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ModuleStatement extends BaseNop {

    public static final String INSTRUCTION = "MODULE";

    public ModuleStatement(String name) {
        super(name);
    }
}
