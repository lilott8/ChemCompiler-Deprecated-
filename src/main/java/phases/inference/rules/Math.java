package phases.inference.rules;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.satsolver.strategies.SolverStrategy;
import substance.Property;

import static typesystem.epa.ChemTypes.*;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "math", ruleType = "term")
public class Math extends NodeAnalyzer {

    public Math(InferenceType type) {
        super(type);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        throw new NotImplementedException();
        // return this;
    }

    public Rule gatherConstraints(InstructionNode node, SolverStrategy solver) {
        for (String out : node.get_def()) {
            this.addConstraint(out, isRealNumber(out) ? REAL : NAT);
        }

        for (String in : node.get_use()) {
            this.addConstraint(in, isRealNumber(in) ? REAL : NAT);
        }

        for (Property prop : node.Instruction().getProperties()) {
            this.addConstraint(CONST, REAL);
        }
        return this;
    }

    @Override
    public Rule gatherUseConstraints(String input) {
        return null;
    }

    @Override
    public Rule gatherDefConstraints(String input) {
        return null;
    }

    @Override
    public Rule gatherConstraints(Property property) {
        return null;
    }
}
