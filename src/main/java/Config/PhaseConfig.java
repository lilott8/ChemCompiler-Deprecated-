package Config;

import java.util.Map;
import java.util.Set;

import Phases.Phase;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface PhaseConfig {
    Set<String> getAllPhases();
    boolean phaseEnabled(String phase);
    boolean phasesEnabled();
}
