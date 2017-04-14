import ChemicalInteractions.ChemicalResolution;
import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.BasicBlock.DependencySlicedBasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.CFGBuilder;
import CompilerDataStructures.InstructionNode;
import CompilerDataStructures.StaticSingleAssignment.MinimalStaticSingleAssignment.MinimalStaticSingleAssignment;
import CompilerDataStructures.StaticSingleAssignment.SemiPrunedStaticSingleAssignment.SemiPrunedStaticSingleAssignment;
import CompilerDataStructures.StaticSingleInstruction.StaticSingleInstruction;
import Translators.TypeSystem.TypeSystemTranslator;
import executable.Experiment;
import manager.Benchtop;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import variable.Variable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class Compiler {
    public static final Logger logger = LogManager.getLogger(Compiler.class);

    private Integer __IDGen;

    private List<CFG> __experimentControlFlowGraphs;
    private CFG __benchtopControlFlowGraph;


    private void initializeData() {
        __IDGen = 0;

        __experimentControlFlowGraphs = new ArrayList<CFG>();
        __benchtopControlFlowGraph = new CFG();

    }


    public Compiler(Benchtop benchtop) {
        try {
            this.initializeData();
            //TODO:: When Incorporating BenchtopCFGs, It is necessary to handle inputs given at Global scope.
            //for (String inputKey : benchtop.getInputs().keySet()) {
             //   __benchtopControlFlowGraph.addResolution(inputKey, benchtop.getInputs().get(inputKey), true);
                //__benchtopControlFlowGraph.addDefinition(inputKey, __benchtopControlFlowGraph.getID());
            //}
            for (String experimentKey : benchtop.getExperiments().keySet()) {
                for (Experiment experiment : benchtop.getExperiments().get(experimentKey)) {
                    CFG controlFlow = CFGBuilder.BuildControlFlowGraph(experiment);
                    //MinimalStaticSingleAssignment SSA = new MinimalStaticSingleAssignment(controlFlow);
                    SemiPrunedStaticSingleAssignment SPSSA = new SemiPrunedStaticSingleAssignment(controlFlow);
                    //StaticSingleInstruction SSI = new StaticSingleInstruction(controlFlow);
                    //System.out.println(controlFlow);
                    for (BasicBlock bb : SPSSA.getBasicBlocks().values()) {
                        //replaces bb with a dependency sliced version
                        SPSSA.newBasicBlock(new DependencySlicedBasicBlock(bb));
                    }

                    //logger.debug("\n" + SSA);
                    logger.debug("\n" + SPSSA);
                    //logger.debug("\n" + SSI);


                    //ProcessExperimentCFG(SPSSA);
                     //__experimentControlFlowGraphs.add(controlFlow);
                    __experimentControlFlowGraphs.add(SPSSA);
                     //logger.debug(controlFlow);

                    //TypeSystemTranslator trans = new TypeSystemTranslator(controlFlow);
                    TypeSystemTranslator trans = new TypeSystemTranslator(SPSSA);
                    trans.toFile("Experiment.txt");

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

    public List<CFG> getExperiments() { return __experimentControlFlowGraphs; }

}