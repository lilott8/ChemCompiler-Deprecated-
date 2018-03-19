package parser;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import chemical.epa.ChemTypes;
import chemical.identification.IdentifierFactory;
import ir.Statement;
import parser.ast.FalseLiteral;
import parser.ast.Identifier;
import parser.ast.IntegerLiteral;
import parser.ast.MatLiteral;
import parser.ast.NatLiteral;
import parser.ast.RealLiteral;
import parser.ast.TrueLiteral;
import parser.visitor.GJNoArguDepthFirst;
import shared.Step;
import shared.variable.Method;
import shared.variable.Property;
import shared.variable.Variable;
import symboltable.SymbolTable;

import static chemical.epa.ChemTypes.BOOL;
import static chemical.epa.ChemTypes.NAT;
import static chemical.epa.ChemTypes.REAL;

/**
 * @created: 2/27/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class BSVisitor extends GJNoArguDepthFirst<BSVisitor> implements Step {

    protected static final String REPEAT = "REPEAT";
    protected static final String BRANCH = "BRANCH";
    protected static final String INTEGER = "INTEGER";
    protected static final String BOOLEAN = "BOOLEAN";
    protected static final String CONST = "CONST";
    private int scopeId = 0;
    private int realId = 0;
    private int booleanId = 0;
    private int integerId = 0;

    private AtomicInteger instructionId = new AtomicInteger(0);

    private Deque<String> scope = new ArrayDeque<>();

    public static final Logger logger = LogManager.getLogger(BSVisitor.class);

    // Keep track of the instruction idCounter to input/outputs
    protected static Map<Integer, Statement> instructions = new LinkedHashMap<>();
    protected static Map<String, Variable> variables = new HashMap<>();
    protected Map<String, Statement> controlInstructions = new HashMap<>();

    // Current instruction to work on.
    protected Statement instruction;
    // Current name to work on.
    protected String name;
    // Constant for a variable.
    protected Variable constant;
    // Store any value of the variable.
    protected String value;
    // Current type(s) of variables.
    protected Set<ChemTypes> types = new HashSet<>();
    // Current method to work on.
    protected Method method;
    // Used for arguments or defining a method.
    protected List<Variable> parameters = new ArrayList<>();
    // Lets us know where to put the argument, if we are invoking.
    protected boolean inInvoke = false;

    // Ability to identify stuff.
    protected chemical.identification.Identifier identifier = IdentifierFactory.getIdentifier();

    {
        this.newScope(SymbolTable.DEFAULT_SCOPE);
    }

    public BSVisitor() {}

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

    protected void addVariable(Variable t) {
        if (!variables.containsKey(t.getScopedName())) {
            variables.put(t.getScopedName(), t);
        } else {
            if (variables.get(t.getScopedName()).equals(t)) {
                logger.warn(String.format("%s is equal to %s", t, variables.get(t.getName())));
            }
        }
    }

    protected void addInstruction(Statement i) {
        instructions.put(i.getId(), i);
        if (!StringUtils.equalsIgnoreCase(this.getCurrentScope(), SymbolTable.DEFAULT_SCOPE)) {
            this.controlInstructions.put(this.getCurrentScope(), i);
        }
    }

    protected String scopifyName() {
        return this.getCurrentScope() + "_" + this.name;
    }

    /**
     * f0 -> <INTEGER_LITERAL>
     */
    @Override
    public BSVisitor visit(IntegerLiteral n) {
        this.name = String.format("%s_%s", CONST, n.f0.toString());
        this.constant = new Property<Integer>(this.name, SymbolTable.INSTANCE.getScopeByName(this.getCurrentScope()));
        this.value = n.f0.toString();
        this.constant.setValue(Integer.parseInt(n.f0.toString()));
        this.constant.addTypingConstraint(NAT);
        this.types.add(NAT);
        SymbolTable.INSTANCE.addLocal(this.constant);
        return this;
    }

    /**
     * f0 -> <NAT>
     */
    @Override
    public BSVisitor visit(NatLiteral n) {
        this.types.add(ChemTypes.NAT);
        return this;
    }

    /**
     * f0 -> <MAT>
     */
    @Override
    public BSVisitor visit(MatLiteral n) {
        this.types.add(ChemTypes.MAT);
        return this;
    }

    /**
     * f0 -> <REAL>
     */
    @Override
    public BSVisitor visit(RealLiteral n) {
        this.types.add(ChemTypes.REAL);
        return this;
    }

    /**
     * f0 -> <TRUE>
     */
    @Override
    public BSVisitor visit(TrueLiteral n) {
        this.name = String.format("%s_%s", CONST, n.f0.toString());
        this.constant = new Property<Boolean>(this.name, SymbolTable.INSTANCE.getScopeByName(this.getCurrentScope()));
        this.value = "true";
        this.constant.setValue(true);
        this.constant.addTypingConstraint(BOOL);
        this.types.add(ChemTypes.BOOL);
        SymbolTable.INSTANCE.addLocal(this.constant);
        return this;
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public BSVisitor visit(FalseLiteral n) {
        this.name = String.format("%s_%s", CONST, n.f0.toString());
        this.constant = new Property<Boolean>(this.name, SymbolTable.INSTANCE.getScopeByName(this.getCurrentScope()));
        this.value = "false";
        this.constant.setValue(false);
        this.constant.addTypingConstraint(BOOL);
        this.types.add(ChemTypes.BOOL);
        SymbolTable.INSTANCE.addLocal(this.constant);
        this.types.add(ChemTypes.BOOL);
        return this;
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    @Override
    public BSVisitor visit(Identifier n) {
        if (this.types.contains(REAL)) {
            this.name = String.format("%s_%d", REAL, realId++);
        } else if (this.types.contains(NAT)) {
            this.name = String.format("%s_%d", INTEGER, integerId++);
        } else if (this.types.contains(BOOL)) {
            this.name = String.format("%s_%d", BOOLEAN, booleanId++);
        } else {
            this.name = n.f0.toString();
        }


        // This allows us to save arguments to functions.
        if (this.inInvoke) {
            String varName = String.format("%s_%s", this.getCurrentScope(), this.name);
            logger.warn(varName);
            logger.warn(SymbolTable.INSTANCE.getSymbols());
            Variable v = SymbolTable.INSTANCE.getSymbol(varName);
            logger.info("In inInvoke, thus adding: " + v.getName());
            this.parameters.add(v);
        }
        return this;
    }

    protected Set<ChemTypes> getTypingConstraints(Variable t) {
        if (BSVisitor.variables.containsKey(t.getScopedName())) {
            return BSVisitor.variables.get(t.getScopedName()).getTypes();
        } else {
            return this.identifier.identifyCompoundForTypes(t.getName());
        }
    }

    protected int getNextIntId() {
        return this.integerId++;
    }

    protected int getNextRealId() {
        return this.realId++;
    }

    protected int getNextScopeId() {
        return this.scopeId++;
    }

    protected int getNextBoolId() {
        return this.booleanId++;
    }

    protected int getNextInstructionId() {
        return this.instructionId.getAndIncrement();
    }

    protected int getCurrentId() {
        return this.instructionId.get();
    }
}
