package utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import config.PhaseConfig;
import phases.PhaseFacade;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TestConfig implements PhaseConfig {

    List<String> files = new ArrayList<>();
    Set<PhaseFacade.PHASES> phases = new HashSet<>();

    public TestConfig(String file) {
        files.add(file);
        phases.add(PhaseFacade.PHASES.INFERENCE);
    }

    @Override
    public List<String> getFilesForCompilation() {
        return files;
    }

    @Override
    public Set<PhaseFacade.PHASES> getAllPhases() {
        return phases;
    }

    @Override
    public boolean phaseEnabled(PhaseFacade.PHASES phase) {
        return this.phases.contains(phase);
    }

    @Override
    public boolean phasesEnabled() {
        return !this.phases.isEmpty();
    }

    @Override
    public String getOutputDir() {
        return null;
    }

    @Override
    public boolean clean() {
        return false;
    }

    @Override
    public boolean isDebug() {
        return false;
    }

    @Override
    public int getNumberOfThreads() {
        return 0;
    }

    @Override
    public boolean monitorResources() {
        return false;
    }
}
