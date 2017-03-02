package StaticSingleInstruction.StaticSingleAssignment;

import StaticSingleInstruction.InstructionNode;

import java.util.ArrayList;

public class PHIInstruction extends  InstructionNode{

    protected String __outputSymbol;
    protected ArrayList<String> __joinedSymbols;

    public PHIInstruction(){
        super(-1,null);
    }
}