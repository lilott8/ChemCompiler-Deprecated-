package phases.inference.satsolver.constraints;

/**
 * @created: 10/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class MixSMT extends MatSMT {

    public MixSMT(String key, ConstraintType type) {
        super(key, type);
    }

    @Override
    public String buildDeclares() {
        StringBuilder sb = new StringBuilder();
        sb.append(super.buildDeclares());

        return sb.toString();
    }
}
