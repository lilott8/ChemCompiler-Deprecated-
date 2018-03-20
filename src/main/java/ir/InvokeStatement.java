package ir;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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

        logger.info(this.inputVariables);
        logger.info(this.method.getIndexedParameters());

        int comma = 0;
        for (Statement s : this.method.getStatements()) {
            logger.info("Inputs: " + s);
            // The list of new variables to be used.
            List<Variable> variables = new ArrayList<>();
            // Easy way to iterate the statements input variables.
            for (int x = 0; x < s.getInputVariables().size(); x++) {
                // We know that if it is in the parameters, then we need to replace it.
                if (this.method.getParameters().containsKey(s.getInputVariables().get(x).getName())) {
                    int counter = 0;
                    for (Variable getIndex : this.method.getIndexedParameters()) {
                        if (StringUtils.equalsIgnoreCase(getIndex.getName(), s.getInputVariables().get(x).getName())) {
                            logger.info("Found a match: " + getIndex.getName() + "/" + s.getInputVariables().get(x).getName() + " with count @: " + counter);
                            variables.add(this.inputVariables.get(counter));
                            logger.warn("Replacing: " + s.getInputVariables().get(x).getName() + " with: " + this.inputVariables.get(counter).getName());
                        } else {
                            logger.info(getIndex.getName() + " is not equal to: " + s.getInputVariables().get(x).getName());
                        }
                        counter++;
                    }
                } else {
                    logger.info("We can't find: " + s.getInputVariables().get(x));
                    variables.add(s.getInputVariables().get(x));
                }
            }
            s.clearInputVariables();
            s.addInputVariables(variables);
            sb.append(s.toJson());
            if (comma < this.method.getStatements().size() - 1) {
                sb.append(",").append(NL);
                comma++;
            }
        }

        if (!this.method.getReturnStatement().getOutputVariable().getTypes().contains(ChemTypes.getNums())) {
            sb.append(",").append(NL);
            MixStatement statement = new MixStatement();
            statement.addInputVariable(this.method.getReturnStatement().getOutputVariable());
            statement.addInputVariable(this.method.getReturnStatement().getOutputVariable());
            statement.addOutputVariable(this.outputVariable);
            sb.append(statement.toJson());
        }

        return sb.toString();
    }
}
