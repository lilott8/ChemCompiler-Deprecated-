package ir;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import chemical.epa.ChemTypes;
import shared.errors.InvalidSyntaxException;
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
    private Map<String, Variable> scopeMatcher = new HashMap<>();

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

        if (this.inputVariables.isEmpty()) {
            logger.warn("Input variables to invoke is empty???");
        } else { logger.info(this.inputVariables);}

        for (Statement s : this.method.getStatements()) {
            if (this.inputVariables.size() != s.getInputVariables().size()) {
                logger.fatal("How are the invocation inputs not the same size");
            }
            // Mutate the statement here!
            List<Variable> variables = new ArrayList<>();
            List<Variable> inputs = s.getInputVariables();
            for (int x = 0; x < s.getInputVariables().size(); x++) {
                logger.info(String.format("Input: %s", inputs.get(x).getName()));
                if (this.method.getParameters().containsKey(inputs.get(x).getName())) {
                    logger.info(String.format("Converting: %s to %s", inputs.get(x).getName(), this.method.getParameters().get(inputs.get(x).getName())));
                    variables.add(this.method.getParameters().get(inputs.get(x).getName()));
                } else {
                    variables.add(inputs.get(x));
                }
            }
            s.clearInputVariables();
            s.addInputVariables(variables);
            sb.append(s.toJson());
        }

        if (!this.method.getReturnStatement().getOutputVariable().getTypes().contains(ChemTypes.getNums())) {
            sb.append(",").append(NL);
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
