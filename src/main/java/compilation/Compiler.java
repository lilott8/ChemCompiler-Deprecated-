package compilation;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.List;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.basicblock.DependencySlicedBasicBlock;
import compilation.datastructures.CFGBuilder;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.ssi.StaticSingleInformation;
import config.Config;
import config.ConfigFactory;
import executable.Experiment;
import manager.Benchtop;
import parsing.BioScript.BenchtopParser;
import phases.Phase;
import phases.PhaseFacade;
import shared.Facade;
import translators.TranslatorFacade;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class Compiler {
    public static final Logger logger = LogManager.getLogger(Compiler.class);

    private Integer __IDGen = 0;

    private List<CFG> __experimentControlFlowGraphs = new ArrayList<>();
    private CFG __benchtopControlFlowGraph = new CFG();

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
        //this.initializeData();
    }

    @Deprecated
    private void initializeData() {
        //__IDGen = 0;

        //__experimentControlFlowGraphs = new ArrayList<CFG>();
        //__benchtopControlFlowGraph = new CFG();

    }

    public void compile() {
        try {
            //TODO: When Incorporating BenchtopCFGs, It is necessary to handle inputs given at Global scope.
            //for (String inputKey : benchtop.getInputs().keySet()) {
            //   __benchtopControlFlowGraph.addResolution(inputKey, benchtop.getInputs().get(inputKey), true);
            //__benchtopControlFlowGraph.addDefinition(inputKey, __benchtopControlFlowGraph.getID());
            //}
            for (String experimentKey : this.benchtop.getExperiments().keySet()) {
                for (Experiment experiment : this.benchtop.getExperiments().get(experimentKey)) {
                    this.controlFlow = CFGBuilder.BuildControlFlowGraph(experiment);
                    //logger.info(this.controlFlow.toString());
                    //minimumssa SSA = new minimumssa(controlFlow);
                    //semiprunedssa SPSSA = new semiprunedssa(controlFlow);
                    this.SSI = new StaticSingleInformation(this.controlFlow);
                    //System.out.println(controlFlow);

                    //replaces basic blocks with dependancy sliced versions
                    for (BasicBlock bb : this.SSI.getBasicBlocks().values()) {
                        this.SSI.newBasicBlock(new DependencySlicedBasicBlock(bb, this.SSI));
                    }

                    DependencySlicedBasicBlock.GetInOutSets(this.SSI);

                    //logger.debug("\n" + SSA);
                    //logger.debug("\n" + this.SSI);
                    //logger.debug("\n" + SSI);

                    //ProcessExperimentCFG(SPSSA);
                    //__experimentControlFlowGraphs.add(controlFlow);
                    __experimentControlFlowGraphs.add(this.SSI);
                    //logger.debug(controlFlow);

                    //TypeSystemTranslator trans = new TypeSystemTranslator(controlFlow);
                    /*if (config.INSTANCE.translationsEnabled() && config.INSTANCE.translationEnabled(config.TRANSLATORS.TYPSYSTEM)) {
                        config.INSTANCE.getTranslationByName(config.TRANSLATORS.TYPSYSTEM).runTranslation(this.SSI).toFile(config.INSTANCE.getOuptutDir() + "experiment.txt");
                        //Translator trans = new TypeSystemTranslator().runTranslation(SSI);
                        //trans.toFile("Experiment.txt");
                    }*/

                    //trans.toFile("Experiment3.txt");

                    //TypeSystemTranslator input = TypeSystemTranslator.readFromFile("TestTransfer.txt");

                    //logger.fatal(trans);
                }
            }
            //  logger.info(__variableTable);
        } catch (Exception e) {
            logger.fatal(e);
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
            logger.info("Phases are set to be run.");
            for (CFG experiment : this.__experimentControlFlowGraphs) {
                Facade phase = new PhaseFacade(ConfigFactory.getConfig(), experiment);
                phase.start();
            }
        }
    }

    public void runTranslations() {
        if (ConfigFactory.getConfig().translationsEnabled()) {
            logger.info("Translators are set to be run.");
            for (CFG experiment : this.__experimentControlFlowGraphs) {
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

    public List<CFG> getExperiments() { return __experimentControlFlowGraphs; }

}