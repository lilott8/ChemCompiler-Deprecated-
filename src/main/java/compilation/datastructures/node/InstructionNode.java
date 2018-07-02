package compilation.datastructures.node;

//import chemicalInteractions.ChemicalInteraction;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import executable.instructions.Instruction;
import substance.Property;

/**
 * Created by chriscurtis on 9/28/16.
 */
public class InstructionNode implements Serializable, Node {

    public static final Logger logger = LogManager.getLogger(InstructionNode.class);

    protected List<String> inputSymbols = new ArrayList<>();
    protected List<String> outputSymbols = new ArrayList<>();
    private Integer id;
    private Instruction instruction;
    private Set<String> dispenseSymbols = new LinkedHashSet<>();
    private Set<String> inSet = new LinkedHashSet<>();
    private Set<String> outSet = new LinkedHashSet<>();
    private Set<String> def = new LinkedHashSet<>();
    private Set<String> use = new LinkedHashSet<>();
    private Set<InstructionNode> predecessors = new LinkedHashSet<>();
    private Set<InstructionNode> successors = new LinkedHashSet<>();
    private boolean leader = false;

    public InstructionNode(Integer id, Instruction instruction) {
        this.id = id;
        this.instruction = instruction;
        stripInputsAndOutputs(instruction);
    }

    public InstructionNode(Integer id, Instruction instruction, Boolean isLeader) {
        this.id = id;
        this.instruction = instruction;
        leader = isLeader;
        stripInputsAndOutputs(instruction);
    }

    public Set<String> getInSet() {
        return inSet;
    }

    public Set<String> getOutSet() {
        return outSet;
    }

    public Set<String> getDef() {
        return def;
    }

    public void setDef(Set<String> def) {
        this.def = new LinkedHashSet<>(def);
    }

    public Set<String> getUse() {
        return use;
    }

    public void setUse(Set<String> use) {
        this.use = new LinkedHashSet<>(use);
    }

    public Set<InstructionNode> getPred() {
        return predecessors;
    }

    public Set<InstructionNode> getSucc() {
        return successors;
    }

    public Integer getId() {
        return id;
    }

    public Instruction getInstruction() {
        return instruction;
    }
    //public ChemicalInteraction getChemicalInteraction() {return __interaction; }

    //public void addChemicalInteraction(ChemicalInteraction ci) { __interaction = ci; }
    public void setLeader(boolean isleader) {
        leader = isleader;
    }

    public Boolean isLeader() {
        return leader;
    }

    public void addImplicitDispense(String symbol) {
        this.dispenseSymbols.add(symbol);
    }

    public void addTransferIn(String symbol) {
        this.inputSymbols.add(symbol);
    }

    public List<String> getInputSymbols() {
        return inputSymbols;
    }

    public List<String> getOutputSymbols() {
        return outputSymbols;
    }

    public Set<String> getDispenseSymbols() {
        return dispenseSymbols;
    }

    public String toString() {
        return this.toString("");
    }

    public String toString(String indentBuffer) {
        StringBuilder sb = new StringBuilder();
        sb.append(indentBuffer).append(id.toString()).append(":\t");

        String ret = indentBuffer + id.toString() + ":\t";
        for (String out : outputSymbols) {
            ret += out + " = ";
            sb.append(out).append(" = ");
        }

        if (instruction != null) {
            ret += instruction.getName() + " ";
            sb.append(instruction.getName());
        }

        for (String input : inputSymbols) {
            ret += " \"" + input + "\"";
        }


        if (instruction != null)
            for (Property property : instruction.getProperties())
                ret += ", " + property.toString();

        return ret;
    }


    private void stripInputsAndOutputs(Instruction instruction) {
        if (instruction == null) {
            return;
        }
        inputSymbols.addAll(instruction.getInputs().keySet());
        outputSymbols.addAll(instruction.getOutputs().keySet());
    }

}
