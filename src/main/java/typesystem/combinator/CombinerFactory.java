package typesystem.combinator;

import config.ConfigFactory;
import config.InferenceConfig;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class CombinerFactory {

    private static InferenceConfig config = ConfigFactory.getConfig();
    private static final Combiner combiner;

    static {
        if (config.simulateChemistry()) {
            combiner = new ChemAxonCombiner();
        } else {
            combiner = new NaiveCombiner();
        }
    }

    public static Combiner getCombiner() {
        return combiner;
    }

}
