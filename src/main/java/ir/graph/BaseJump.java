package ir.graph;

/**
 * @created: 3/8/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BaseJump extends BaseStatement implements Jump {

    private String target;

    protected BaseJump(String name) {
        super(name);
    }

    @Override
    public String getTarget() {
        return this.target;
    }

    @Override
    public void setTarget(String target) {
        this.target = target;
    }
}
