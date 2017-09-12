package phases.inference.rules;

import compilation.datastructures.basicblock.BasicBlockEdge;
import phases.inference.Inference;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class EdgeAnalyzer extends Rule {

    protected static int counter = 0;

    public EdgeAnalyzer(Inference.InferenceType type) {
        super(type);
    }
    public EdgeAnalyzer(Inference.InferenceType type, Class<? extends EdgeAnalyzer> clazz) {
        super(type, clazz);
    }

    public abstract Rule gatherConstraints(BasicBlockEdge edge);

    protected int getAndIncrement() {
        return counter++;
    }

    protected int get() {
        return counter;
    }
}
