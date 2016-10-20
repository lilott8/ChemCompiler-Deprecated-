import CFGBuilder.*;
import ChemicalInteractions.ChemicalInteraction;
import ChemicalInteractions.ChemicalResolution;
import SymbolTable.NestedSymbolTable;
import executable.Executable;
import executable.Experiment;
import executable.instructions.*;
import manager.Benchtop;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import substance.Chemical;
import substance.Substance;
import variable.Instance;
import variable.Variable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

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
                this.addResolution(inputKey,benchtop.getInputs().get(inputKey),__benchtopControlFlowGraph, true);
                __benchtopControlFlowGraph.addDefinition(inputKey,-1);
            }

            for(String experimentKey :  benchtop.getExperiments().keySet()) {
                for (Experiment experiment : benchtop.getExperiments().get(experimentKey)) {
                    NestedSymbolTable experiementTable = new NestedSymbolTable();
                    experiementTable.setParent(__benchtopControlFlowGraph.getSymbolTable());
                    CFG controlFlow = CFGBuilder.BuildControlFlowGraph(experiment.getInstructions(), experiementTable);
                    ProcessExperimentCFG(controlFlow,experiment);

                    __experimentControlFlowGraphs.add(controlFlow);
                    logger.info(controlFlow);

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
        for(String inputKey: experiment.getInputs().keySet()) {
            controlFlowGraph.addDefinition(inputKey);
            this.addResolution(inputKey,experiment.getInputs().get(inputKey),controlFlowGraph,true);
        }
        for (BasicBlock bb : controlFlowGraph.getBasicBlocks()) {
            ProcessBasicBlockInstructions(controlFlowGraph, bb);
        }
    }

    private void ProcessBasicBlockInstructions(CFG controlFlowGraph, BasicBlock bb) {
//Since Processing instructions can possibly add implict dispense nodes. I am pulling the instruction list first then processing on the static list.
        List<InstructionNode> nodes = new ArrayList<InstructionNode>();
        for(InstructionNode node : bb.getInstructions()) {
            nodes.add(node);
        }

        for(InstructionNode node : nodes) {
            List<Variable> instructionInputs = ProcessOperationInput(controlFlowGraph, bb, node);
            ProcessOperationOutput(controlFlowGraph, bb, node , instructionInputs);

        /*
         *        ChemicalInteraction interaction = null;
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
         */
        }
    }

    private List<Variable> ProcessOperationInput( CFG controlFlowGraph, BasicBlock basicBlock, InstructionNode node){
        //TODO:: Insert Implicit Dispense Nodes!
        List<Variable> instructionInputs = new ArrayList<Variable>();

        for(String inputKey : node.Instruction().getInputs().keySet()) {
            Variable input = node.Instruction().getInputs().get(inputKey);
            instructionInputs.add(input);


            //check to see if the input is GlobalDeclaaration
            if (controlFlowGraph.getSymbolTable().contains(inputKey)) {
                if(controlFlowGraph.getSymbolTable().get(inputKey).IsGlobal()) {
                    logger.warn("Should create implicit Dispense for: " + inputKey);
                    Dispense disp = new Dispense(controlFlowGraph.getNewID(),"dispense: "+ inputKey);
                    InstructionNode dispenseNode = new InstructionNode(controlFlowGraph.getNewID(), disp);
                    basicBlock.addInstruction( dispenseNode);
                    controlFlowGraph.addUse(inputKey,dispenseNode.ID());
                }
            }
            //Check to see if someone already used the variable. if so ad Edge
            if (controlFlowGraph.getUseTable().containsKey(inputKey)) {

                int lastElement = controlFlowGraph.getUseTable().get(inputKey).size() - 1;

                if(lastElement >= 0)
                    basicBlock.AddEdge(controlFlowGraph.getUseTable().get(inputKey).get(lastElement),node.ID());
            }else if(controlFlowGraph.getDefintionTable().containsKey(inputKey)) {
                int definitionLocation = controlFlowGraph.getDefintionTable().get(inputKey).size() - 1;
                if(definitionLocation >= 0)
                    basicBlock.AddEdge(controlFlowGraph.getDefintionTable().get(inputKey).get(definitionLocation),node.ID());
            }

            //TODO::Check to see if Input is a partial reference, if so do not update tracking
            //TODO::If Ansestor has a branch add to list of possible uses, not concrete.
            //Add/Update the usage of the variable.
            controlFlowGraph.addUse(inputKey,node.ID());
        }
        return instructionInputs;
    }


    private void ProcessOperationOutput(CFG controlFlowGraph, BasicBlock basicBlock, InstructionNode node, List<Variable> instructionInputs){
        //check for outputs
        for (String outputKey: node.Instruction().getOutputs().keySet()) {
            Variable output = node.Instruction().getOutputs().get(outputKey);
            controlFlowGraph.addDefinition(outputKey,node.ID());


            //create Chemical Resolution
            ChemicalResolution resolution = new ChemicalResolution(output.getName());

            for(Variable variable : instructionInputs){
                resolution.addReference(ResolveVariable(variable,controlFlowGraph));
            }

            controlFlowGraph.getSymbolTable().put(outputKey,resolution);

        }
    }







    //TODO::Once substance refrence is resolved this can be fixed.
    private ChemicalResolution ResolveVariable(Variable variable, CFG controlFlowGraph) {
        if(controlFlowGraph.getSymbolTable().contains(variable.getId()))
            return controlFlowGraph.getSymbolTable().get(variable.getId());

        ChemicalResolution resolution = new ChemicalResolution(variable.getName());
        if(variable instanceof Instance) {
            logger.info("Found Instance Literal");
            resolution.setIsLiteral(false);
        }

        for(Substance v : variable.getSubstance().values()) {
            resolution.addReference(ResolveSubstance(v,controlFlowGraph));
        }
        return resolution;
    }

    private ChemicalResolution ResolveSubstance(Substance substance, CFG controlFlowGraph){
        if(controlFlowGraph.getSymbolTable().contains(substance.getName()))
            return controlFlowGraph.getSymbolTable().get(substance.getName());

        ChemicalResolution resolution = new ChemicalResolution(substance.getName());
        resolution.setIsLiteral(true);
        for(Chemical c: substance.getChemicals().values())
            resolution.addLiteral(c);

        controlFlowGraph.getSymbolTable().put(substance.getName(),resolution);
        return resolution;
    }

    private void addResolution(String key, Variable variable, CFG controlFlowGraph){
       this.addResolution(key,variable,controlFlowGraph, false);
    }

    private void addResolution(String key, Variable variable, CFG controlFlowGraph, Boolean isGlobal){
        ChemicalResolution resolution = ResolveVariable(variable, controlFlowGraph);
        resolution.setisGlobal(isGlobal);
        controlFlowGraph.getSymbolTable().put(key, resolution);
    }


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
*/