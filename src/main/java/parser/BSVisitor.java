package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import chemical.identification.IdentifierFactory;
import parser.visitor.GJNoArguDepthFirst;
import shared.Step;
import shared.variable.Variable;
import typesystem.elements.Formula;

/**
 * @created: 2/27/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BSVisitor extends GJNoArguDepthFirst<BSVisitor> implements Step {

    private Deque<String> scope = new ArrayDeque<>();

    public static final Logger logger = LogManager.getLogger(BSVisitor.class);

    // Keep track of the instruction id to input/outputs
    protected static Map<Integer, Formula> instructions = new LinkedHashMap<>();
    protected static Map<String, Variable> variables = new HashMap<>();

    protected Formula instruction;

    // Ability to identify stuff.
    protected chemical.identification.Identifier identifier = IdentifierFactory.getIdentifier();

    protected String getCurrentScope() {
        return this.scope.peek();
    }

    protected String newScope(String name) {
        // Push the new scope onto the stack.
        this.scope.push(name);
        // Return the scope we are in.
        return this.scope.peek();
    }

    protected String endScope() {
        // Remove the most recent element.
        this.scope.pop();
        // Return the context we return to.
        return this.scope.peek();
    }

    protected static void addVariable(Variable t) {
        if (!variables.containsKey(t.getScopedName())) {
            variables.put(t.getScopedName(), t);
        } else {
            if (variables.get(t.getScopedName()).equals(t)) {
                logger.warn(String.format("%s is equal to %s", t, variables.get(t.getName())));
            }
        }
    }

    protected static void addInstruction(Formula i) {
        instructions.put(i.getId(), i);
    }
}
