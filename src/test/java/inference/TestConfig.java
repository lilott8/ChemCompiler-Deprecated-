package inference;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import config.InputConfig;
import config.PhaseConfig;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TestConfig implements InputConfig, PhaseConfig {

    List<String> files = new ArrayList<>();
    Set<String> phases = new HashSet<>();

    public TestConfig(String file) {
        files.add(file);
        phases.add("inference");
    }

    @Override
    public List<String> getFilesForCompilation() {
        return files;
    }

    @Override
    public Set<String> getAllPhases() {
        return phases;
    }

    @Override
    public boolean phaseEnabled(String phase) {
        return this.phases.contains(phase);
    }

    @Override
    public boolean phasesEnabled() {
        return !this.phases.isEmpty();
    }
}
