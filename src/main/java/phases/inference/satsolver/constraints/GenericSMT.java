package phases.inference.satsolver.constraints;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.Set;

import phases.inference.satsolver.strategies.Z3Strategy;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class GenericSMT extends Constraint {
    private Set<ChemTypes> chems = new HashSet<>();
    private Set<ChemTypes> nums = new HashSet<>();
    private String varName = "";
    private ConstraintType type;
    public static final String TAB = "\t";
    public static final String NL = System.lineSeparator();


    public GenericSMT(String name, ConstraintType type) {
        super(name, type);
        //this.varName = StringUtils.replaceAll(name, " ", "_");
        //this.type = type;
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

    private String buildBasicAsserts() {
        StringBuilder sb = new StringBuilder();
        return sb.toString();
    }

    public String buildDeclares() {
        StringBuilder sb = new StringBuilder();
        return sb.toString();
    }

    public String buildMembership() {
        StringBuilder sb = new StringBuilder();
        if (this.chems.size() == 1) {
            for (ChemTypes t : this.chems) {
                sb.append("(= ").append(getAssertName(t.toString())).append(" ").append("true").append(")").append(System.lineSeparator());
            }
        } else {
            //logger.info("We have membership");
        }
        return sb.toString();
    }

    public String buildImplication() {
        StringBuilder sb = new StringBuilder();
        return sb.toString();
    }

    public String buildSubset() {
        StringBuilder sb = new StringBuilder();
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
        StringBuilder sb = new StringBuilder();
        // sb.append(this.buildDeclares());
        sb.append(this.buildBasicAsserts());
        //sb.append("(assert ").append(System.lineSeparator()).append("\t");
        //sb.append(this.buildMembership()).append(")").append(System.lineSeparator());
        return sb.toString();
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

    @Override
    public String buildConstraintValues() {
        return this.buildBasicAsserts();
    }

    public String buildAsserts() {
        StringBuilder sb = new StringBuilder();

        if (!this.chems.isEmpty()) {

            //sb.append()
        }
        if (!this.nums.isEmpty()) {
            for (ChemTypes t : this.nums) {
                sb.append(t).append(NL);
            }
        }


        return sb.toString();
    }
}
