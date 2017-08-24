package phases.inference.satsolver;

import com.microsoft.z3.Context;

/**
 * @created: 8/24/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Z3Solver implements Solver<Context> {

    private Context context;

    public Z3Solver() {
        this.context = new Context();
    }

    @Override
    public Context getSolver() {
        return this.context;
    }
}
