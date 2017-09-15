package phases.inference;

import org.apache.commons.lang3.StringUtils;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import phases.inference.satsolver.strategies.Z3Strategy;
import typesystem.epa.ChemTypes;
import typesystem.epa.EpaManager;
import typesystem.epa.Reaction;

/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SMTConstraint implements Constraint {
    private Set<ChemTypes> chems = new HashSet<>();
    private Set<ChemTypes> nums = new HashSet<>();
    private String varName = "";

    private String simpleAsserts = "";
    private String declares = "";
    private String asserts = "";
    boolean isChemical = true;

    public SMTConstraint(String name) {
        this.varName = StringUtils.replaceAll(name, " ", "_");
    }

    public void addConstraint(ChemTypes type) {
        if (!ChemTypes.isNumber(type)) {
            this.chems.add(type);
        } else {
            this.nums.add(type);
        }
    }

    public void addConstraints(Set<ChemTypes> types) {
        for (ChemTypes t : types) {
            this.addConstraint(t);
        }
    }

    private String getAssertName(String append) {
        return this.varName + "_" + append;
    }

    private String buildBasicAsserts() {
        StringBuilder sb = new StringBuilder();
        for (ChemTypes t : this.chems) {
            sb.append("(assert (= ").append(getAssertName(t.toString())).append(" true))").append(System.lineSeparator());
        }
        for (ChemTypes t : this.nums) {
            sb.append("(assert (= ").append(this.varName).append(" ").append(t).append("))").append(System.lineSeparator());
        }
        return sb.toString();
    }

    private String buildDeclares() {
        StringBuilder sb = new StringBuilder();

        for (ChemTypes t : this.chems) {
            sb.append("(declare-const ").append(getAssertName(t.toString())).append(" Bool)").append(System.lineSeparator());
        }
        for (ChemTypes t : this.nums) {
            sb.append("(declare-const ").append(varName).append(" ").append(Z3Strategy.numType).append(")").append(System.lineSeparator());
        }

        return sb.toString();
    }

    private String buildConstraintAsserts() {
        StringBuilder sb = new StringBuilder();

        // See if we have anything in here, if we don't we don't need to visit here.
        if (!this.chems.isEmpty()) {
            // Handles the open assert( and(not.... statements.
            StringBuilder conjunctiveHeader = new StringBuilder();
            // Handles closing the appropriate parens from above.
            StringBuilder conjunctiveFooter = new StringBuilder();
            // Handles the (assert (= x y)).
            StringBuilder conjunctiveAsserts = new StringBuilder();
            // Handles the (assert (= x true)), (assert (= y true)).
            StringBuilder chemAsserts = new StringBuilder();
            boolean append = false;

            for (ChemTypes constraint : this.chems) {
                /*for (Map.Entry<ChemTypes, Reaction> entry : EpaManager.INSTANCE.groupMap.entrySet())
                sb.append("(assert (= ").append(constraint.toString()).append(" true))").append(System.lineSeparator());
                //if (!EpaManager.INSTANCE.test())
                if (!ChemTypes.illegalCombos.get(constraint).isEmpty()) {
                    append = true;
                    for (ChemTypes illegal : ChemTypes.illegalCombos.get(constraint)) {
                        chemAsserts.append("(assert (= ").append(illegal).append(" true))").append(System.lineSeparator());
                        // Add the comparative asserts
                        conjunctiveAsserts.append("\t\t\t(= ").append(getAssertName(constraint.toString())).append(" ").append(illegal).append(")").append(System.lineSeparator());
                    }
                }*/
            }
            sb.append(chemAsserts);
            if (append) {
                // Begin assert.
                conjunctiveHeader.append("(assert").append(System.lineSeparator());
                // Begin not.
                //conjunctiveHeader.append("\t(not").append(System.lineSeparator());
                // Begin and.
                conjunctiveHeader.append("\t\t(and").append(System.lineSeparator());
                // End and.
                conjunctiveFooter.append("\t\t)").append(System.lineSeparator());
                // End not.
                //conjunctiveFooter.append("\t)").append(System.lineSeparator());

                // End assert.
                conjunctiveFooter.append(")").append(System.lineSeparator());
                sb.append(conjunctiveHeader).append(conjunctiveAsserts).append(conjunctiveFooter);
            }
        }
        for (ChemTypes t : this.nums) {
            sb.append("(assert (= ").append(this.varName).append(" ").append(t).append("))").append(System.lineSeparator());
        }
        return sb.toString();
    }

    private String buildChemIllegalAssert() {
        StringBuilder sb = new StringBuilder();

        return sb.toString();
    }

    @Override
    public Set<ChemTypes> getConstraints() {
        Set<ChemTypes> temp = new HashSet<>();
        temp.addAll(this.chems);
        temp.addAll(this.nums);
        return temp;
    }

    @Override
    public String buildOutput() {
        return this.buildDeclares() + this.buildBasicAsserts() + this.buildConstraintAsserts();
    }

    public String toString() {
        StringBuilder sb = new StringBuilder(this.varName).append(": ").append(System.lineSeparator());
        for (ChemTypes t : this.chems) {
            sb.append("\t").append(t).append(System.lineSeparator());
        }
        for (ChemTypes t : this.nums) {
            sb.append("\t").append(t).append(System.lineSeparator());
        }
        return sb.toString();
    }
}
