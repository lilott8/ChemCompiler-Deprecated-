import ChemicalInteractions.ChemicalResolution;
import StaticSingleInstruction.BasicBlock.BasicBlock;
import StaticSingleInstruction.ControlFlowGraph.CFG;
import StaticSingleInstruction.CFGBuilder;
import StaticSingleInstruction.InstructionNode;
import StaticSingleInstruction.StaticSingleAssignment.StaticSingleAssignment;
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
                    StaticSingleAssignment SSA = new StaticSingleAssignment(controlFlow);

                    //System.out.println(controlFlow);
                    logger.debug("\n" + SSA);
                    //System.out.print(controlFlow.getDominatorTree().toString());

                    //ProcessExperimentCFG(controlFlow, experiment);
                     //__experimentControlFlowGraphs.add(controlFlow);
                     //logger.debug(controlFlow);

                    //TypeSystemTranslator trans = new TypeSystemTranslator(controlFlow);

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

    private void ProcessExperimentCFG(CFG controlFlowGraph, Experiment experiment) {
        //Global Input Chemicals
        for (String inputKey : experiment.getInputs().keySet()) {
            controlFlowGraph.addResolution(inputKey, experiment.getInputs().get(inputKey), true);
            controlFlowGraph.getSymbolTable().addDefinition(inputKey, controlFlowGraph.getID());
        }

        Boolean changed = true;
        while (changed) {
            changed = false;
            for (BasicBlock bb : controlFlowGraph.getBasicBlocks().values()) {
                //clear old usage information on consecutive passes.
                bb.getSymbolTable().clear();
                if (ProcessBasicBlockInstructions(controlFlowGraph, bb))
                    changed = true;
                //logger.info(bb.metaToString());
            }
        }
    }

    private Boolean ProcessBasicBlockInstructions(CFG controlFlowGraph, BasicBlock bb) {
        Boolean changed = false;
        ArrayList<BasicBlock> predecessors = new ArrayList<BasicBlock>();

        if (controlFlowGraph.hasPredecessors(bb.ID())) {
            for (Integer predecessor : controlFlowGraph.getPredecessors(bb.ID()))
                predecessors.add(controlFlowGraph.getBasicBlock(predecessor));
        }
        if (bb.processPredecessors(predecessors))
            changed = true;

        List<InstructionNode> nodes = new ArrayList<InstructionNode>();
        for (InstructionNode node : bb.getInstructions()) {
            nodes.add(node);
        }
        bb.getEdges().clear();
        for (InstructionNode node : nodes) {
            Collection<Variable> instructionInputs = node.Instruction().getInputs().values();

            ProcessOperationInput(controlFlowGraph, bb, node);
            ProcessOperationOutput(controlFlowGraph, bb, node, instructionInputs);
        }

        if (bb.processOutput())
            changed = true;

        return changed;
    }

    private void ProcessOperationInput(CFG controlFlowGraph, BasicBlock basicBlock, InstructionNode node) {
        //TODO:: Insert Implicit Dispense Nodes!
        for (String inputKey : node.Instruction().getInputs().keySet()) {

            if (basicBlock.getSymbolTable().getUsagedTable().containsKey(inputKey)) {
                Integer lastUsedIn = basicBlock.getSymbolTable().lastUsedIn(inputKey);
                if (lastUsedIn < 0) {
                    // A negative usage indicates that the Chemical was killed. so check at global

                    logger.fatal("Found ODD getID in Usage table:" + lastUsedIn + "For: " + inputKey);
                } else {
                    basicBlock.addEdge(lastUsedIn, node.ID());
                    basicBlock.updateUsage(inputKey, node);
                }
            } else if (basicBlock.getSymbolTable().getDefinitionTable().containsKey(inputKey)) {
                //fresh definition without usage
                Integer definedIn = basicBlock.getSymbolTable().getDefinitionID(inputKey);

                basicBlock.addEdge(definedIn, node.ID());
                basicBlock.updateUsage(inputKey, node);

            } else if (basicBlock.getBasicBlockEntryTable().containsKey(inputKey)) {
                //could have multiple areas it is coming from.
                Set<Integer> entrySet = basicBlock.getBasicBlockEntryUsage(inputKey);
                if (entrySet.size() > 2) {
                    logger.warn("PHI NODE");
                }
                for (Integer entry : entrySet) {
                    if (entry == -2)
                        node.addImplicitDispense(inputKey);
                    if(!basicBlock.getSymbolTable().contains(inputKey) || !basicBlock.getSymbolTable().get(inputKey).IsStationary())
                        basicBlock.addEdge(entry, node.ID());
                    //if(node.Instruction().getInputs().get(inputKey) instanceof Instance && ((Instance)node.Instruction().getInputs().get(inputKey)).getIsStationary() )
                        basicBlock.updateUsage(inputKey, node);
                }
            } else {

                logger.warn(inputKey + ", was not mapped anywhere, treating as an implicit dispense");
                node.addImplicitDispense(inputKey);
                basicBlock.addEdge(-2, node.ID());
                //basicBlock.updateUsage(inputKey, node);
            }
        }
    }


    private void ProcessOperationOutput(CFG controlFlowGraph, BasicBlock basicBlock, InstructionNode node, Collection<Variable> instructionInputs) {
        //check for outputs
        for (String outputKey : node.Instruction().getOutputs().keySet()) {
            Variable output = node.Instruction().getOutputs().get(outputKey);
            basicBlock.getSymbolTable().addDefinition(outputKey, node.ID());
            if(basicBlock.getSymbolTable().getUsagedTable().containsKey(outputKey))
                basicBlock.getSymbolTable().getUsagedTable().put(outputKey,node.ID());

            //create Chemical Resolution
            ChemicalResolution resolution = new ChemicalResolution(outputKey);

            //this may need to point to the basic block symbol table not the cfg one
            for (Variable variable : instructionInputs) {
                resolution.addReference(controlFlowGraph.ResolveVariable(variable));
            }

            basicBlock.getSymbolTable().put(outputKey, resolution);
            //controlFlowGraph.getSymbolTable().put(outputKey,resolution);

        }

    }
}