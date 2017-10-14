package phases.inference.elements;

import org.apache.commons.lang.SystemUtils;

import java.util.ArrayList;
import java.util.List;

/**
 * @created: 10/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Instruction {

    public final int id;
    public final String instructionName;
    private List<Variable> output = new ArrayList<>();
    private List<Variable> input = new ArrayList<>();


    public Instruction(int id, String instructionName) {
        this.id = id;
        this.instructionName = instructionName;
    }

    public Instruction addOutputTerm(Variable output) {
        this.output.add(output);
        return this;
    }

    public Instruction addInputTerm(Variable input) {
        this.input.add(input);
        return this;
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
        sb.append("ID: ").append(this.id).append("\tType: ").append(this.instructionName).append(System.lineSeparator());
        sb.append("Inputs: ").append(this.input).append(System.lineSeparator());
        sb.append("Outputs: ").append(this.output).append(System.lineSeparator());
        sb.append("===================").append(System.lineSeparator());

        return sb.toString();
    }
}
