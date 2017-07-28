package Phases.Inference.Rules.Instructions;

import java.util.ArrayList;
import java.util.List;

import CompilerDataStructures.BasicBlock.BasicBlock;
import Phases.Inference.Constraint;
import Phases.Inference.Rules.InferenceInstruction;
import Phases.Inference.Rules.InferenceTerm;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Detect<T> implements InferenceInstruction, InferenceTerm {

    private List<Constraint<InferenceTerm>> constraints = new ArrayList<Constraint<InferenceTerm>>();
    private Constraint<String> termTyping = new Constraint<String>("a", "a");

    public Detect() {

    }

    public Detect(List<Constraint<InferenceTerm>> constraints, Constraint<String> termTyping) {
        this.constraints = constraints;
    }

    public Constraint<String> getTermTyping() {
        return this.termTyping;
    }

    public List<Constraint<InferenceTerm>> getConstraints() {
        return this.constraints;
    }

    public boolean isApplicable(BasicBlock block) {
        return false;
    }

    public void parseInstruction(BasicBlock block) {

    }
}
