package typesystem.classification;

import config.ConfigFactory;
import config.InferenceConfig;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ClassifierFactory {
    private static InferenceConfig config = ConfigFactory.getConfig();
    private static final Classifier classifier;

    static {
        if (config.buildFilters()) {
            classifier = new ChemAxonClassifier();
        } else {
            classifier = new NaiveClassifier();
        }
    }

    public static Classifier getClassifier() {
        return classifier;
    }

}
