package phases.inference.satsolver.constraints;

import org.apache.commons.lang3.StringUtils;

import java.util.HashSet;
import java.util.Set;

import typesystem.epa.ChemTypes;

/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class Constraint {

    protected Set<ChemTypes> constraints = new HashSet<>();
    protected String varName = "";
    private ConstraintType type;
    public static final String TAB = "\t";
    public static final String NL = System.lineSeparator();

    public enum ConstraintType {
        ASSIGN, MIX, CONST, SPLIT, NUMBER, DETECT, HEAT, OUTPUT, STORE
    }

    // For debugging stuff.
    public abstract String buildDeclares();
    public abstract String buildConstraintValues();
    public abstract String buildAsserts();

    Constraint(String key, ConstraintType type) {
        this.varName = StringUtils.replaceAll(key, " ", "_");;
        this.type = type;
    }

    protected String getAssertName(String append) {
        return this.varName + "_" + append;
    }

    protected String getAssertName(ChemTypes append) {
        return this.varName + "_" + append.toString();
    }

    public String buildOutput() {
        return this.buildDeclares() + this.buildConstraintValues() + this.buildAsserts();
    }

    public void addConstraint(ChemTypes type) {
        this.constraints.add(type);
    }

    public void addConstraints(Set<ChemTypes> types) {
        this.constraints.addAll(types);
    }

    public Set<ChemTypes> getConstraints() {
        return this.constraints;
    }
}
