package phases.inference.rules;

import org.apache.commons.lang3.StringUtils;

import compilation.datastructures.InstructionNode;
import compilation.datastructures.basicblock.BasicBlockEdge;
import phases.inference.Inference.InferenceType;
import phases.inference.elements.Instruction;
import phases.inference.elements.Term;
import phases.inference.elements.Variable;
import phases.inference.satsolver.constraints.Constraint;
import substance.Property;
import typesystem.epa.ChemTypes;

import static typesystem.epa.ChemTypes.NAT;
import static typesystem.epa.ChemTypes.REAL;


/**
 * @created: 7/27/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
@InferenceRule(ruleName = "elseif", ruleType = "instruction", analyze = "edge")
public class ElseIfBranch extends EdgeAnalyzer {

    public ElseIfBranch(InferenceType type) {
        super(type, ElseIfBranch.class);
    }

    private IfBranch branch = new IfBranch(InferenceType.INSTRUCTION);

    @Override
    public Rule gatherConstraints(BasicBlockEdge edge) {
        return this.branch.gatherConstraints(edge);
    }
}
