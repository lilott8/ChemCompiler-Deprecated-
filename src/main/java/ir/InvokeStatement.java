package ir;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import chemical.epa.ChemTypes;
import shared.variable.Method;
import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class InvokeStatement extends BaseStatement implements Invoke {

    public static final Logger logger = LogManager.getLogger(InvokeStatement.class);

    private Method method;

    public InvokeStatement(Method method) {
        super(method.getName());
        this.method = method;
        this.containsInvoke = true;
    }

    @Override
    public Method getMethod() {
        return this.method;
    }

    @Override
    public String compose(Formula instruction) {
        return super.defaultCompose(instruction);
    }

    @Override
    public String compose(Variable variable) {
        return super.defaultCompose(variable);
    }

    @Override
    public String toJson() {
        return this.toJson("");
    }

    @Override
    public String toJson(String indent) {
        StringBuilder sb = new StringBuilder("");

        for (Statement s : this.method.getStatements()) {
            sb.append(s.toJson());
        }

        if (!this.method.getReturnStatement().getOutputVariable().getTypes().contains(ChemTypes.getNums())) {
            MixStatement statement = new MixStatement();
            statement.addInputVariable(this.method.getReturnStatement().getOutputVariable());
            statement.addInputVariable(this.method.getReturnStatement().getOutputVariable());
            statement.addOutputVariable(this.outputVariable);
            sb.append(statement.toJson());
        }

        //logger.info(sb.toString());

        return sb.toString();
    }
}
