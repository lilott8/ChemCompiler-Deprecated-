package config;

import org.apache.commons.lang3.StringUtils;

/**
 * @created: 9/7/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface InferenceConfig extends CommonConfig {

    /**
     * Handles the level of inference resolution:
     *   - Generic:
     *     Resolves generic types: MAT, REAL, NAT.
     *   - Union:
     *     Resolves the reactive type to which the chemical belongs.
     */
    enum InferenceLevel {
        GENERIC, UNION
    }

    InferenceLevel getInferenceLevel();
}
