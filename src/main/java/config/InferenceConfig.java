package config;

import org.apache.commons.lang3.StringUtils;

/**
 * @created: 9/7/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface InferenceConfig extends CommonConfig {
    int getClassificationLevel();
    boolean ignoreWarnings();
    boolean buildFilters();
    String getEpaDefs();
    boolean simulateChemistry();
}
