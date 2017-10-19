package shared;

import java.util.List;
import java.util.Set;

import typesystem.epa.ChemTypes;

/**
 * @created: 10/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class VarConstraints {

    private List<Tuple<String, Set<ChemTypes>>> inputs;
    private List<Tuple<String, Set<ChemTypes>>> outputs;
    private String var;

    public VarConstraints(String var, List<Tuple<String, Set<ChemTypes>>> input, List<Tuple<String, Set<ChemTypes>>> output) {
        this.inputs = input;
        this.outputs = output;
        this.var = var;
    }

    public String getVar() {
        return var;
    }

    public List<Tuple<String, Set<ChemTypes>>> getInputs() {
        return inputs;
    }

    public List<Tuple<String, Set<ChemTypes>>> getOutputs() {
        return outputs;
    }
}
