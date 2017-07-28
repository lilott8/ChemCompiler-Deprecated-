package Phases.Inference.Rules.Terms;

import java.util.List;

import CompilerDataStructures.BasicBlock.BasicBlock;
import Phases.Inference.Constraint;
import Phases.Inference.Rules.InferenceTerm;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Real implements InferenceTerm {


    public Real() {
    }

    public Real(Constraint<InferenceTerm> constraint) {

    }

    public Constraint<String> getTermTyping() {
        return null;
    }

    public List<Constraint<InferenceTerm>> getConstraints() {
        return null;
    }

    public boolean isApplicable(BasicBlock block) {
        return false;
    }

    public void parseInstruction(BasicBlock block) {

    }
}
