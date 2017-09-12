package config;

import java.util.Set;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface PhaseConfig extends CommonConfig {
    Set<String> getAllPhases();
    boolean phaseEnabled(String phase);
    boolean phasesEnabled();

}
