package CFGBuilder;

import SymbolTable.NestedSymbolTable;

import java.util.ArrayList;

/**
 * Created by chriscurtis on 9/29/16.
 */
public class BasicBlock {
    private ArrayList<InstructionNode> __instructions;
    private ArrayList<InstructionEdge> __edges;
    private Integer __ID;

    public BasicBlock(Integer id){
        __instructions = new ArrayList<InstructionNode>();
        __edges = new ArrayList<InstructionEdge>();
        __ID = id;
    }

    public BasicBlock(BasicBlock bb) {
        __instructions = bb.getInstructions();
        __edges = bb.getEdges();
        __ID = bb.ID();
    }

    public void addInstruction(InstructionNode instruction) {
        __instructions.add(instruction);
    }

    public void addInstruction(int index, InstructionNode instruction) {
        __instructions.add(index, instruction);
    }

    public void AddEdge(InstructionNode source, InstructionNode destination) {
        this.AddEdge(source.ID(),destination.ID());
    }
    public void AddEdge(Integer source, Integer destination) {
        __edges.add(new InstructionEdge(source,destination));
    }


    public ArrayList<InstructionNode> getInstructions() { return __instructions; }
    public ArrayList<InstructionEdge> getEdges() {return __edges; }

    public Integer ID(){
        return __ID;
    }

    public  String toString() {
        return this.toString("");
    }
    public  String toString(String indentBuffer) {
        String ret = indentBuffer + "Basic Block : " + __ID.toString() + '\n';

        ret += indentBuffer + '\t' + "Instructions: \n";
        for(InstructionNode node : __instructions)
            ret += node.toString(indentBuffer+'\t'+'\t') +'\n';

        ret += indentBuffer +'\t' + "Edges: \n";
        for(InstructionEdge edge : __edges)
            ret += edge.toString(indentBuffer+'\t'+'\t') + '\n';

        return ret;
    }
}