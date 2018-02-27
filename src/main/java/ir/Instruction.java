package ir;

import java.util.ArrayList;
import java.util.List;
import shared.variable.Variable;

/**
 * @created: 2/26/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Instruction {

    private static int instructionCounter = 0;
    protected final int id;

    protected List<Variable> output = new ArrayList<>();
    protected List<Variable> input = new ArrayList<>();
    protected List<Variable> properties = new ArrayList<>();

    protected Instruction() {
        this.id = instructionCounter++;
    }

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

    public List<Variable> getOutput() {
        return this.output;
    }
    public List<Variable> getInput() {
        return this.input;
    }

    public List<Variable> getProperties() {
        return this.properties;
    }
}
