package typesystem.elements;

import java.util.ArrayList;
import java.util.List;

import typesystem.rules.Rule;
import shared.Variable;

/**
 * @created: 10/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Instruction {

    private static int instructionCounter = 0;
    public final Rule.InstructionType type;
    public final int id;
    private List<Variable> output = new ArrayList<>();
    private List<Variable> input = new ArrayList<>();
    private List<Variable> properties = new ArrayList<>();


    public Instruction(Rule.InstructionType type){
        this.type = type;
        this.id = instructionCounter++;
    }


    /*public Instruction(int id, Rule.InstructionType type) {
        this.id = id;
        this.type = type;
    }*/

    public Instruction addOutputVariable(Variable output) {
        this.output.add(output);
        return this;
    }

    public Instruction addInputVariable(Variable input) {
        this.input.add(input);
        return this;
    }

    public Instruction addProperty(Variable prop) {
        this.properties.add(prop);
        return this;
    }

    public int getId() {
        return this.id;
    }

    public Rule.InstructionType getType() {
        return this.type;
    }

    public List<Variable> getProperties() {
        return this.properties;
    }

    public List<Variable> getOutput() {
        return this.output;
    }

    public List<Variable> getInput() {
        return this.input;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("===================").append(System.lineSeparator());
        sb.append("getId: ").append(this.id).append("\tVisibility: ").append(this.type).append(System.lineSeparator());
        sb.append("Inputs: ").append(this.input).append(System.lineSeparator());
        sb.append("Outputs: ").append(this.output).append(System.lineSeparator());
        sb.append("===================").append(System.lineSeparator());

        return sb.toString();
    }
}
