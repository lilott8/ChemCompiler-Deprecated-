package ir.soot;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ir.soot.instruction.Instruction;
import shared.variable.Variable;
import shared.variable.Method;

/**
 * @created: 2/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Experiment {

    public static final Logger logger = LogManager.getLogger(Experiment.class);

    private String name = "";

    private long id = -1;
    private Map<String, Variable> manifest = new HashMap<>();
    private Map<String, Variable> stationary = new HashMap<>();
    private Map<String, Variable> modules = new HashMap<>();
    private List<Instruction> instructions = new ArrayList<>();
    private Map<String, Method> methods = new HashMap<>();

    public Experiment(long id) {
        this.id = id;
    }

    public Experiment(String name) {
        this.name = name;
        this.id = -1;
    }

    public Experiment(long id, String name) {
        this.name = name;
        this.id = id;
    }

    public long getId() {
        return id;
    }

    public String getName() {
        return this.name;
    }

    public void addInstructions(List<Instruction> instructions) {
        for(Instruction i : instructions) {
            this.addInstruction(i);
        }
    }

    public List<Instruction> getInstructions() {
        return instructions;
    }

    public void addInstruction(Instruction e) {
        this.instructions.add(e);
    }

    public void addManifest(Variable v) {
        this.manifest.put(v.getScopedName(), v);
    }

    public void addModule(Variable v) {
        this.modules.put(v.getScopedName(), v);
    }

    public void addStationary(Variable v) {
        this.stationary.put(v.getScopedName(), v);
    }

    public void addMethods(Method v) {
        this.methods.put(v.getName(), v);
    }

    public String toString() {
        return this.manifest.toString();
    }
}
