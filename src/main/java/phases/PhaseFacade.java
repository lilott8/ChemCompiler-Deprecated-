package phases;

import org.apache.commons.lang3.StringUtils;

import java.util.HashMap;
import java.util.Map;

import compilation.datastructures.cfg.CFG;
import config.PhaseConfig;
import phases.inference.Inference;
import shared.Facade;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class PhaseFacade implements Facade {

    public enum PHASES {
        INFERENCE, NONE;

        public static Phase getPhase(PHASES p) {
            switch (p) {
                default:
                case INFERENCE:
                    return new Inference();
            }
        }
    }

    private PhaseConfig config;
    private Map<PHASES, Phase> phases = new HashMap<PHASES, Phase>();
    private CFG controlFlowGraph;

    public PhaseFacade(PhaseConfig config, CFG cfg) {
        this.controlFlowGraph = cfg;
        this.config = config;

        for(String s : this.config.getAllPhases()) {
            PHASES t = PHASES.valueOf(StringUtils.upperCase(s));
            this.phases.put(t, PHASES.getPhase(t));
        }
    }

    public void start() {
        for(Map.Entry<PHASES, Phase> p : this.phases.entrySet()) {
            p.getValue().runPhase(this.controlFlowGraph);
        }
    }
}
