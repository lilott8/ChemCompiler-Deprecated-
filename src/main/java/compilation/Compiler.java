package compilation;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.List;

import compilation.datastructures.CFGBuilder;
import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.basicblock.DependencySlicedBasicBlock;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.ssi.StaticSingleInformation;
import config.Config;
import config.ConfigFactory;
import executable.Experiment;
import manager.Benchtop;
import parsing.BioScript.BenchtopParser;
import phases.PhaseFacade;
import shared.Facade;
import translators.TranslatorFacade;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class Compiler {
    public static final Logger logger = LogManager.getLogger(Compiler.class);

    private Integer idGen = 0;

    private List<CFG> experimentControlFlowGraphs = new ArrayList<>();
    private CFG benchtopControlFlowGraph = new CFG();

    private Benchtop benchtop;
    private StaticSingleInformation SSI;
    private CFG controlFlow;

    public Compiler(Config config) {
        try {
            for(String file : config.getFilesForCompilation()) {
                BenchtopParser.parse(file);
            }
        }
        catch (Exception e) {
            logger.fatal(e.getMessage());
            logger.fatal("Exception: ", e);
        }
        this.benchtop = Benchtop.INSTANCE;
    }

    public void compile() {
        try {
            for (String experimentKey : this.benchtop.getExperiments().keySet()) {
                for (Experiment experiment : this.benchtop.getExperiments().get(experimentKey)) {
                    this.controlFlow = CFGBuilder.buildControlFlowGraph(experiment);
                    this.SSI = new StaticSingleInformation(this.controlFlow);

                    //replaces basic blocks with dependancy sliced versions
                    for (BasicBlock bb : this.SSI.getBasicBlocks().values()) {
                        this.SSI.newBasicBlock(new DependencySlicedBasicBlock(bb, this.SSI));
                    }

                    DependencySlicedBasicBlock.getInOutSets(this.SSI);
                    experimentControlFlowGraphs.add(this.SSI);
                }
            }
        } catch (Exception e) {
            logger.fatal(e);
            e.printStackTrace();
        }

        //runPhases();
        //runTranslations();
    }

    public void runAllOps() {
        this.runPhases();
        this.runTranslations();
    }

    public void runPhases() {
        if (ConfigFactory.getConfig().phasesEnabled()) {
            if (ConfigFactory.getConfig().isDebug()) {
                // logger.info("Phases set to run: " + ConfigFactory.getConfig().getAllPhases());
            }
            for (CFG experiment : this.experimentControlFlowGraphs) {
                Facade phase = new PhaseFacade(ConfigFactory.getConfig(), experiment);
                phase.start();
            }
        }
    }

    public void runTranslations() {
        if (ConfigFactory.getConfig().translationsEnabled()) {
            if (ConfigFactory.getConfig().isDebug()) {
                // logger.info("Translators are set to be run.");
            }
            for (CFG experiment : this.experimentControlFlowGraphs) {
                Facade translator = new TranslatorFacade(ConfigFactory.getConfig(), experiment);
                translator.start();
            }
        }
    }

    public StaticSingleInformation getSSI() {
        return this.SSI;
    }

    public CFG getControlFlow() {
        return this.controlFlow;
    }

    public List<CFG> getExperiments() {
        return experimentControlFlowGraphs;
    }
}