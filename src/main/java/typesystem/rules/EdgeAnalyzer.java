package typesystem.rules;

import compilation.datastructures.basicblock.BasicBlockEdge;
import typesystem.Inference;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class EdgeAnalyzer extends Rule {

    public EdgeAnalyzer(Inference.InferenceType type) {
        super(type);
    }

    public EdgeAnalyzer(Inference.InferenceType type, Class<? extends EdgeAnalyzer> clazz) {
        super(type, clazz);
    }

    public abstract Rule gatherConstraints(BasicBlockEdge edge);
}
