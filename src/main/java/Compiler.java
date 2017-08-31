import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.BasicBlock.DependencySlicedBasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.CFGBuilder;import CompilerDataStructures.StaticSingleInformation.StaticSingleInformation;
import Config.Config;
import executable.Experiment;
import manager.Benchtop;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import java.util.ArrayList;
import java.util.List;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class Compiler {
    public static final Logger logger = LogManager.getLogger(Compiler.class);

    private Integer __IDGen;

    private List<CFG> __experimentControlFlowGraphs;
    private CFG __benchtopControlFlowGraph;

    private Benchtop benchtop;
    private StaticSingleInformation SSI;
    private CFG controlFlow;

    private void initializeData() {
        __IDGen = 0;

        __experimentControlFlowGraphs = new ArrayList<CFG>();
        __benchtopControlFlowGraph = new CFG();

    }

    public void compile() {
        try {
            //TODO:: When Incorporating BenchtopCFGs, It is necessary to handle inputs given at Global scope.
            //for (String inputKey : benchtop.getInputs().keySet()) {
            //   __benchtopControlFlowGraph.addResolution(inputKey, benchtop.getInputs().get(inputKey), true);
            //__benchtopControlFlowGraph.addDefinition(inputKey, __benchtopControlFlowGraph.getID());
            //}
            for (String experimentKey : this.benchtop.getExperiments().keySet()) {
                for (Experiment experiment : this.benchtop.getExperiments().get(experimentKey)) {
                    this.controlFlow = CFGBuilder.BuildControlFlowGraph(experiment);
                    //MinimalStaticSingleAssignment SSA = new MinimalStaticSingleAssignment(controlFlow);
                    //SemiPrunedStaticSingleAssignment SPSSA = new SemiPrunedStaticSingleAssignment(controlFlow);
                    this.SSI = new StaticSingleInformation(this.controlFlow);
                    //System.out.println(controlFlow);

                    //replaces basic blocks with dependancy sliced versions
                    for (BasicBlock bb : this.SSI.getBasicBlocks().values()) {
                        this.SSI.newBasicBlock(new DependencySlicedBasicBlock(bb, this.SSI));
                    }

                    DependencySlicedBasicBlock.GetInOutSets(this.SSI);

                    //logger.debug("\n" + SSA);
                    logger.debug("\n" + this.SSI);
                    //logger.debug("\n" + SSI);

                    //ProcessExperimentCFG(SPSSA);
                    //__experimentControlFlowGraphs.add(controlFlow);
                    __experimentControlFlowGraphs.add(this.SSI);
                    //logger.debug(controlFlow);

                    //TypeSystemTranslator trans = new TypeSystemTranslator(controlFlow);
                    if (Config.INSTANCE.translationsEnabled() && Config.INSTANCE.translationEnabled("typesystem")) {
                        Config.INSTANCE.getTranslationByName("typesystem").runTranslation(this.SSI).toFile(Config.INSTANCE.getOuptutDir() + "experiment.txt");
                        //Translator trans = new TypeSystemTranslator().runTranslation(SSI);
                        //trans.toFile("Experiment.txt");
                    }

                    //trans.toFile("Experiment3.txt");

                    //TypeSystemTranslator input = TypeSystemTranslator.readFromFile("TestTransfer.txt");

                    //logger.fatal(trans);
                }
            }
            //  logger.info(__variableTable);
        } catch (Exception e) {
            System.out.println(e);
            logger.fatal(e);
            e.printStackTrace();
        }
    }

    public Compiler(Benchtop benchtop) {
        this.benchtop = benchtop;
        this.initializeData();
    }

    public StaticSingleInformation getSSI() {
        return this.SSI;
    }

    public CFG getControlFlow() {
        return this.controlFlow;
    }

    public List<CFG> getExperiments() { return __experimentControlFlowGraphs; }

}