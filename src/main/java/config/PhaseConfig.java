package config;

import java.util.Set;

import phases.PhaseFacade;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface PhaseConfig extends CommonConfig {
    Set<PhaseFacade.PHASES> getAllPhases();
    boolean phaseEnabled(PhaseFacade.PHASES phase);
    boolean phasesEnabled();

}
