import ChemicalInteractions.ChemicalResolution;
import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.CFG;
import ControlFlowGraph.CFGBuilder;
import ControlFlowGraph.InstructionNode;
import Translators.TypeSystemTanslator;
import executable.Experiment;
import executable.instructions.Combine;
import executable.instructions.Output;
import executable.instructions.Split;
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
    //private NestedSymbolTable __symbolTable;
  //  private HashMap<String, ChemicalResolution > __chemicalResolutions;
   // private HashMap<String,Substance> __substanceResolution;

    private List<CFG> __experimentControlFlowGraphs;
    private CFG __benchtopControlFlowGraph;


    private void initializeData(){
        __IDGen =0;

        //__chemicalResolutions = new HashMap<String, ChemicalResolution> ();
       // __substanceResolution = new HashMap<String, Substance>();

        __experimentControlFlowGraphs = new ArrayList<CFG>();
        __benchtopControlFlowGraph = new CFG();

    }


    public Compiler(Benchtop benchtop)
    {
        try{
            this.initializeData();

            for(String inputKey: benchtop.getInputs().keySet()) {
                __benchtopControlFlowGraph.addResolution(inputKey,benchtop.getInputs().get(inputKey), true);
                __benchtopControlFlowGraph.addDefinition(inputKey,__benchtopControlFlowGraph.ID());
            }
            for(String experimentKey :  benchtop.getExperiments().keySet()) {
                for (Experiment experiment : benchtop.getExperiments().get(experimentKey)) {
                    CFG controlFlow = CFGBuilder.BuildControlFlowGraph(experiment.getInstructions());
                    ProcessExperimentCFG(controlFlow,experiment);
                    __experimentControlFlowGraphs.add(controlFlow);
                    logger.info(controlFlow);
                    TypeSystemTanslator trans = new TypeSystemTanslator(controlFlow);

                    logger.debug(trans);
                }
            }
          //  logger.info(__variableTable);
        }
        catch(Exception e) {
            System.out.println(e);
            logger.fatal(e);
            logger.fatal(e.getStackTrace().toString());
        }

    }


    private void ProcessExperimentCFG(CFG controlFlowGraph, Experiment experiment){
        //Global Input Chemicals
        for(String inputKey: experiment.getInputs().keySet()) {
            controlFlowGraph.addResolution(inputKey,experiment.getInputs().get(inputKey),true);
            controlFlowGraph.getSymbolTable().addDefinition(inputKey, controlFlowGraph.ID());
        }

        Boolean changed = true;
        while(changed) {
            changed = false;
            for (BasicBlock bb : controlFlowGraph.getBasicBlocks()) {
                //clear old usage information on consecutive passes.
                bb.getSymbolTable().clear();
                if(ProcessBasicBlockInstructions(controlFlowGraph, bb))
                    changed = true;
                //logger.info(bb.metaToString());
            }
        }
    }

    private Boolean ProcessBasicBlockInstructions(CFG controlFlowGraph, BasicBlock bb) {
        Boolean changed = false;
        ArrayList<BasicBlock> predecessors = new ArrayList<BasicBlock>();

        if(controlFlowGraph.hasPredecessors(bb.ID())) {
            for (Integer predecessor : controlFlowGraph.getPredecessors(bb.ID()))
                predecessors.add(controlFlowGraph.getBasicBlock(predecessor));
        }
        if(bb.processPredecessors(predecessors))
            changed = true;

        List<InstructionNode> nodes = new ArrayList<InstructionNode>();
        for(InstructionNode node : bb.getInstructions()) {
            nodes.add(node);
        }
        bb.getEdges().clear();
        for(InstructionNode node : nodes) {
            Collection<Variable> instructionInputs = node.Instruction().getInputs().values();

            ProcessOperationInput(controlFlowGraph, bb, node);
            ProcessOperationOutput(controlFlowGraph, bb, node , instructionInputs);
        }

        if(bb.processOutput())
            changed = true;

        return changed;
    }

    private void ProcessOperationInput( CFG controlFlowGraph, BasicBlock basicBlock, InstructionNode node){
        //TODO:: Insert Implicit Dispense Nodes!
        for(String inputKey : node.Instruction().getInputs().keySet()) {

            if(basicBlock.getSymbolTable().getUsagedTable().containsKey(inputKey)){
                Integer lastUsedIn =  basicBlock.getSymbolTable().lastUsedIn(inputKey);
                if(lastUsedIn < 0) {
                    // A negative usage indicates that the Chemical was killed. so check at global

                    logger.fatal("Found ODD ID in Usage table:" + lastUsedIn + "For: " + inputKey);
                }
                else {
                    basicBlock.addEdge(lastUsedIn, node.ID());
                    basicBlock.updateUsage(inputKey, node);
                }
            }
            else if(basicBlock.getSymbolTable().getDefinitionTable().containsKey(inputKey)){
                //fresh definition without usage
                Integer definedIn = basicBlock.getSymbolTable().getDefinitionID(inputKey);

                basicBlock.addEdge(definedIn,node.ID());
                basicBlock.updateUsage(inputKey,node);

            }
            else if(basicBlock.getBasicBlockEntryTable().containsKey(inputKey)) {
                //could have multiple areas it is coming from.
                Set<Integer> entrySet = basicBlock.getBasicBlockEntryUsage(inputKey);
                if(entrySet.size() > 2){
                    logger.warn("PHI NODE");
                }
                for(Integer entry : entrySet){
                    basicBlock.addEdge(entry,node.ID());
                    basicBlock.updateUsage(inputKey,node);
                }
            }
            else {
                logger.warn("Found:" + inputKey +": It was not mapped anywhere!");
            }
        }
    }


    private void ProcessOperationOutput(CFG controlFlowGraph, BasicBlock basicBlock, InstructionNode node, Collection<Variable> instructionInputs){
        //check for outputs
        for (String outputKey: node.Instruction().getOutputs().keySet()) {
            Variable output = node.Instruction().getOutputs().get(outputKey);
            basicBlock.getSymbolTable().addDefinition(outputKey,node.ID());


            //create Chemical Resolution
            ChemicalResolution resolution = new ChemicalResolution(outputKey);

            //this may need to point to the basic block symbol table not the cfg one
            for(Variable variable : instructionInputs){
                resolution.addReference(controlFlowGraph.ResolveVariable(variable));
            }

            basicBlock.getSymbolTable().put(outputKey,resolution);
            //controlFlowGraph.getSymbolTable().put(outputKey,resolution);

        }

    }







    //TODO::Once substance refrence is resolved this can be fixed.



    public void generateMFSimFile() throws Exception
    {
        if(__experimentControlFlowGraphs == null)
            logger.fatal("Control Flow Graph was NULL");
        throw new Exception("Not Yet Implemented");

    }
    public void generateTypeSystemFile() throws Exception
    {
        if(__experimentControlFlowGraphs == null)
            logger.fatal("Control Flow Graph was NULL");
        throw new Exception("Not Yet Implemented");




    }
}
   /* private CFG ProcessExperiment(Experiment experiment) {
        CFG controlFlowGraph = new CFG();
        BasicBlock currentBB = new BasicBlock(__IDGen++);

        for(String inputKey: experiment.getInputs().keySet()) {
            controlFlowGraph.addDefinition(inputKey,currentBB.ID());
            this.addResolution(inputKey,experiment.getInputs().get(inputKey));
        }

        for (Executable i :experiment.getInstructions()) {
            if(i instanceof Instruction) {
               ProcessInstruction(controlFlowGraph,currentBB,(Instruction) i);
            }
        }

       // controlFlowGraph.AddBasicBlock(currentBB);

        logger.info(currentBB);
        return controlFlowGraph;
    }*/
       /*private void ProcessInstruction(CFG controlFlowGraph, BasicBlock basicBlock, Instruction instruction) {
        InstructionNode node = new InstructionNode(__IDGen++, instruction);

        //List<Variable> instructionInputs = ProcessOperationInput(controlFlowGraph, basicBlock, instruction, node.ID());


        //ProcessOperationOutput(controlFlowGraph, basicBlock, instruction, node.ID(), instructionInputs);


        basicBlock.addInstruction(node);
        ChemicalInteraction interaction = null;
        if (instruction instanceof Combine )
            interaction = new ChemicalInteraction(node.ID(), ChemicalInteraction.Operation.MIX);
        else if (instruction instanceof Heat)
            interaction = new ChemicalInteraction(node.ID(), ChemicalInteraction.Operation.HEAT);
        else if (instruction instanceof Detect)
            interaction = new ChemicalInteraction(node.ID(), ChemicalInteraction.Operation.DETECT);
        else if (instruction instanceof Split)
            interaction = new ChemicalInteraction(node.ID(), ChemicalInteraction.Operation.SPLIT);
        else if (instruction instanceof Output)
            interaction = new ChemicalInteraction(node.ID(), ChemicalInteraction.Operation.OUTPUT);


        if (interaction == null )
            return;

        //process chemicals
        for(Variable variable: instructionInputs) {
            logger.info("Resolving" + variable.getName());
                interaction.addChemical(c);

    }


    //TODO::This is something something that still needs to be added into the Framework:
    // https://github.com/lilott8/ChemLibrary/issues/2
    // for(String key : instruction)

        node.addChemicalInteraction(interaction);
}
       /*
            if(basicBlock.getSymbolTable().contains(inputKey)){
                ChemicalResolution inputChemical = basicBlock.getSymbolTable().get(inputKey);
                if(inputChemical.IsGlobal()){
                    // logger.warn("Creating implicit Dispense for: " + inputKey);
                //    Dispense disp = new Dispense(controlFlowGraph.getNewID(), "dispense: " + inputKey);
                //    disp.addOutput(node.Instruction().getInputs().get(inputKey));
                //    InstructionNode dispenseNode = new InstructionNode(controlFlowGraph.getNewID(), disp);

                //    basicBlock.addInstruction(0,dispenseNode);
                    if(! (node.Instruction() instanceof Combine)) {
                        ChemicalResolution res = new ChemicalResolution(inputChemical.getName());
                        for (Chemical c : inputChemical.getLiterals()) {
                            res.addLiteral(c);
                        }
                        for (ChemicalResolution c : inputChemical.getReferences()) {
                            res.addReference(c);
                        }

                        basicBlock.getSymbolTable().put(inputKey, res);

                        basicBlock.getSymbolTable().updateLastUsedIn(inputKey, node.ID());
                    }

                //    basicBlock.addEdge(dispenseNode.ID(),node.ID());
                }
                else {
                    Integer lastUsedIn = basicBlock.getSymbolTable().lastUsedIn(inputKey);
                    //TODO:: this may cause side effect if two of the same sample are passed into the instruction.
                    basicBlock.getSymbolTable().updateLastUsedIn(inputKey,node.ID());
                    basicBlock.addEdge(lastUsedIn,node.ID());
                }
            }
            else if(basicBlock.getSymbolTable().getUsagedTable().containsKey(inputKey)) {
                Integer lastUsed = basicBlock.getSymbolTable().lastUsedIn(inputKey);
                basicBlock.addEdge(lastUsed,node.ID());
                basicBlock.getSymbolTable().updateLastUsedIn(inputKey,node.ID());
            }
            else if(basicBlock.hasIncomingSymbol(inputKey)){
                //this is transferIN and possibly PHI node.
                for(Integer predecessor: basicBlock.getBasicBlockEntryUsage(inputKey)){
                    basicBlock.addEdge(predecessor,node.ID());
                }
                basicBlock.getSymbolTable().updateLastUsedIn(inputKey,node.ID());
            }
            else{
                logger.warn("caught input that is not being processed yet");
                /*Could be chemical literal declared inside instruction*
            }
            */