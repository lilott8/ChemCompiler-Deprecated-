package ir.soot.instruction;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;
import shared.variable.Variable;
import typesystem.satsolver.constraints.SMTSolver;

/**
 * @created: 2/26/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Instruction implements SMTSolver {

    private static int instructionCounter = 0;
    protected final int id;

    protected List<Variable> output = new ArrayList<>();
    protected List<Variable> input = new ArrayList<>();
    protected List<Variable> properties = new ArrayList<>();

    // Assigned type to instruction.
    Set<ChemTypes> type = new HashSet<>();

    protected Instruction() {
        this.id = instructionCounter++;
    }

    public abstract String toJSON();

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

    public Instruction addType(ChemTypes type) {
        this.type.add(type);
        return this;
    }

    public Instruction addTypes(Set<ChemTypes> types) {
        this.type.addAll(types);
        return this;
    }

    public Set<ChemTypes> getTypes() {
        return this.type;
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

    public int getId() {
        return id;
    }
}
