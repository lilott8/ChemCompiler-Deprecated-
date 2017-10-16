package phases.inference.rules;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import compilation.datastructures.InstructionNode;
import phases.inference.Inference.InferenceType;
import phases.inference.satsolver.strategies.SolverStrategy;
import substance.Property;
import phases.inference.satsolver.constraints.Constraint.ConstraintType;

import static typesystem.epa.ChemTypes.*;

/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "math", ruleType = "term")
public class Math extends NodeAnalyzer {

    public Math(InferenceType type) {
        super(type, Math.class);
    }

    @Override
    public Rule gatherAllConstraints(InstructionNode node) {
        throw new NotImplementedException();
        // return this;
    }

    public Rule gatherConstraints(InstructionNode node, SolverStrategy solver) {
        for (String out : node.get_def()) {
            this.addConstraint(out, isRealNumber(out) ? REAL : NAT, ConstraintType.NUMBER);
        }

        for (String in : node.get_use()) {
            this.addConstraint(in, isRealNumber(in) ? REAL : NAT, ConstraintType.NUMBER);
        }

        for (Property prop : node.Instruction().getProperties()) {
            this.addConstraint(Rule.createHash(prop.toString()), REAL, ConstraintType.NUMBER);
        }
        return this;
    }
}
