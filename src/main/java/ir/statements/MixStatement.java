package ir.statements;

import java.util.List;
import java.util.Set;

import chemical.combinator.CombinerFactory;
import chemical.epa.ChemTypes;
import chemical.epa.EpaManager;
import shared.variable.Property;
import shared.variable.Variable;
import typesystem.elements.Formula;
import typesystem.satsolver.strategies.SolverStrategy;

import static typesystem.satsolver.strategies.SolverStrategy.TAB;
import static typesystem.satsolver.strategies.SolverStrategy.getSMTName;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class MixStatement extends BaseStatement {

    public static final String INSTRUCTION = "MIX";

    public MixStatement() {
        super(INSTRUCTION);
    }

    @Override
    public String compose(Formula instruction) {
        StringBuilder sb = new StringBuilder("");

        sb.append("; Building mixes for: ").append(instruction.getId()).append(NL);

        for (Variable v : instruction.getInput()) {
            sb.append(compose(v));
        }

        // There's only one output term here.
        for (Variable v : instruction.getOutput()) {
            sb.append(buildMix(v, instruction.getInput()));
        }

        return sb.toString();
    }

    @Override
    public String compose(Variable variable) {
        StringBuilder sb = new StringBuilder("");

        for (ChemTypes t : (Set<ChemTypes>) variable.getTypes()) {
            sb.append("(assert (= ").append(SolverStrategy.getSMTName(variable.getScopedName(), t)).append(" true))").append(NL);
        }

        return sb.toString();
    }

    private String buildMix(Variable output, List<Variable> input) {
        StringBuilder sb = new StringBuilder("");

        // We need the form: a \in output ^ b \in output => LU(a,b) \subseteq output
        // At this point, output's set contains the look up values already.
        // So we don't need to run it here.  We still need to reference the
        // Lookup table for building the above formula, however.
        boolean killSwitch = false;
        for (Variable input1 : input) {
            for (Variable input2 : input) {
                for (ChemTypes t1 : (Set<ChemTypes>) input1.getTypes()) {
                    for (ChemTypes t2 : (Set<ChemTypes>) input2.getTypes()) {
                        if (!CombinerFactory.getCombiner().combine(t1, t2)) {
                            killSwitch = true;
                        }
                        sb.append(this.buildSimpleImplication(output, input1, input2, t1, t2));
                        //sb.append(this.buildSimpleImplicationWithFalses(output, input1, input2, t1, t2));
                    }
                }
            }
        }
        if (killSwitch) {
            sb.append(killSwitch());
        }
        return sb.toString();
    }


    /**
     * This is the common case! This builds the form: t1 \in output ^ t2 \in output => lu(t1, t2)
     * \subset output Which is: (assert (=> (and (= input1_t1 true) (= input2_t2 true) ) (and (=
     * output_lu(t1, t2) true) ; this will populate for each lu value ) ) )
     */
    private String buildSimpleImplication(Variable output, Variable input1, Variable input2, ChemTypes t1, ChemTypes t2) {
        StringBuilder sb = new StringBuilder("");

        sb.append("(assert").append(NL);
        sb.append(TAB).append("(=>").append(NL);
        sb.append(TAB + TAB).append("(and").append(NL);
        sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(input1.getScopedName(), t1)).append(" true)").append(NL);
        sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(input2.getScopedName(), t2)).append(" true)").append(NL);
        sb.append(TAB + TAB).append(")").append(NL);
        sb.append(TAB + TAB).append("(and").append(NL);
        for (ChemTypes t : EpaManager.INSTANCE.lookUp(t1, t2)) {
            sb.append(TAB + TAB + TAB).append("(= ").append(getSMTName(output.getScopedName(), t)).append(" true)").append(NL);
        }
        sb.append(TAB + TAB).append(")").append(NL);
        //logger.info(String.format("(assert \n\t(=> \n\t\t(and \n\t\t\t(= %s %s) \n\t\t\t(= %s %s)) \n\t\t(and \n\t\t\t(= %s %s)))", getSMTName(input1.getScopedName(), t1), getSMTName(output.getScopedName(), t1), getSMTName(input2.getScopedName(), t2), getSMTName(output.getScopedName(), t2), EpaManager.INSTANCE.lookUp(t1, t2), "?"));
        sb.append(TAB).append(")").append(NL);
        sb.append(")").append(NL);

        return sb.toString();
    }

    @Override
    public String toJson() {
        return this.toJson("");
    }

    @Override
    public String toJson(String indent) {
        // Open the object
        StringBuilder sb = new StringBuilder("{").append(NL);
        // Create the operation.
        sb.append("\"OPERATION\" : {").append(NL);
        sb.append("\"ID\" : ").append(this.id).append(",").append(NL);
        sb.append("\"NAME\" : \"MIX\",").append(NL);
        sb.append("\"CLASSIFICATION\" : \"MIX\",").append(NL);
        sb.append("\"INPUTS\" : [").append(NL);
        int x = 0;
        for (Variable v : this.inputVariables) {
            // Open the object tag.
            sb.append("{").append(NL);
            sb.append(v.buildInput());
            if (!this.properties.isEmpty()) {
                sb.append(",").append(NL);
                if (this.properties.containsKey(Property.TIME)) {
                    sb.append("\"VOLUME\" : {").append(NL);
                    sb.append("\"VALUE\" : ").append(this.properties.get(Property.TIME).getValue()).append(",").append(NL);
                    sb.append("\"UNITS\" : ").append("\"mL\"").append(NL);
                    sb.append("}").append(NL);
                }
            }
            // Close the object tag.
            sb.append("}").append(NL);
            if (x < this.inputVariables.size() - 1) {
                sb.append(",").append(NL);
            }
            x++;
        }
        // Closes the open bracket.
        sb.append("],").append(NL);
        sb.append("\"OUTPUTS\" : [").append(NL);
        // Open the tag.
        sb.append("{").append(NL);
        sb.append(this.outputVariable.redeclare());
        // Close the open tag.
        sb.append("}").append(NL);
        sb.append("]").append(NL);
        // Closes the OPERATION.
        sb.append("}").append(NL);
        // Closes the OBJECT.
        sb.append("}").append(NL);
        return sb.toString();
    }
}
