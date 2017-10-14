package shared;

import java.util.Set;

/**
 * @created: 10/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class InstructionVars {

    private String rule = "";
    private Set<String> inputs;
    private String output = "";

    public InstructionVars(String rule, Set<String> inputs) {
        this.rule = rule;
        this.inputs = inputs;
    }

    public InstructionVars(String rule, Set<String> inputs, String output) {
        this.rule = rule;
        this.output = output;
        this.inputs = inputs;
    }

    public String getRule() {
        return rule;
    }

    public Set<String> getInputs() {
        return inputs;
    }

    public String getOutput() {
        return output;
    }
}
