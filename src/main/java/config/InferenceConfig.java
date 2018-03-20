package config;

import shared.ReportingLevel;

/**
 * @created: 9/7/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface InferenceConfig extends CommonConfig {
    int getClassificationLevel();

    boolean buildFilters();

    ReportingLevel getErrorLevel();

    String getEpaDefs();

    boolean simulateChemistry();

    int smartsLength();

    String getReactiveMatrix();
}
