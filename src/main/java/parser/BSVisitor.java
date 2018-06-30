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
import parser.ast.AndExpression;
import parser.ast.ConditionalParenthesis;
import parser.ast.EqualityExpression;
import parser.ast.FalseLiteral;
import parser.ast.GreaterThanEqualExpression;
import parser.ast.GreaterThanExpression;
import parser.ast.Identifier;
import parser.ast.IntegerLiteral;
import parser.ast.LessThanEqualExpression;
import parser.ast.LessThanExpression;
import parser.ast.MatLiteral;
import parser.ast.MathParenthesis;
import parser.ast.NatLiteral;
import parser.ast.NotEqualExpression;
import parser.ast.NotExpression;
import parser.ast.OrExpression;
import parser.ast.RealLiteral;
import parser.ast.TempUnit;
import parser.ast.TimeUnit;
import parser.ast.TrueLiteral;
import parser.ast.VolumeUnit;
import parser.visitor.GJNoArguDepthFirst;
import shared.Step;
import shared.variable.ConstVariable;
import shared.variable.Method;
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

    public static final Logger logger = LogManager.getLogger(BSVisitor.class);
    public static final String REPEAT = "REPEAT";
    public static final String BRANCH = "BRANCH";
    public static final String INTEGER = "INTEGER";
    public static final String BOOLEAN = "BOOLEAN";
    public static final String CONST = "CONST";
    public static final String TIME = "TIME";
    public static final String VOLUME = "VOLUME";
    public static final String TEMP = "TEMP";
    // Keep track of the instruction idCounter to input/outputs
    protected static Map<Integer, Statement> instructions = new LinkedHashMap<>();
    protected static Map<String, Variable> variables = new HashMap<>();
    protected List<Variable> constants = new ArrayList<>();
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
    // Lets us know if we are parsing a conditional.
    protected boolean inConditional = false;
    // String for the conditional itself.
    protected String conditional = "";
    // Are we in assignment?
    protected boolean isAssign = false;
    // Manage the left hand side of the expression.
    protected Variable assignTo = null;
    // Ability to identify stuff.
    protected chemical.identification.Identifier identifier = IdentifierFactory.getIdentifier();
    private int scopeId = 0;
    private int realId = 0;
    private int booleanId = 0;
    private int integerId = 0;
    protected String units = "";
    protected int integerLiteral = -1;
    protected double realLiteral = -1.0;
    private AtomicInteger instructionId = new AtomicInteger(0);
    private Deque<String> scope = new ArrayDeque<>();

    {
        this.newScope(SymbolTable.DEFAULT_SCOPE);
    }

    public BSVisitor() {
    }

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
                // logger.warn(String.format("%s is equal to %s", t, variables.get(t.getName())));
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
        //this.constant = new ConstVariable<Integer>(this.name, SymbolTable.INSTANCE.getScopeByName(this.getCurrentScope()));
        //this.value = n.f0.toString();
        this.integerLiteral = Integer.parseInt(n.f0.toString());
        //this.constant.setValue(Integer.parseInt(n.f0.toString()));
        //this.constant.addTypingConstraint(NAT);
        this.types.add(NAT);
        //SymbolTable.INSTANCE.addLocal(this.constant);
        //SymbolTable.INSTANCE.addInput(this.constant);
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
        this.constant = new ConstVariable<Boolean>(this.name, SymbolTable.INSTANCE.getScopeByName(this.getCurrentScope()));
        this.value = "true";
        this.constant.setValue(true);
        this.constant.addTypingConstraint(BOOL);
        this.types.add(ChemTypes.BOOL);
        SymbolTable.INSTANCE.addLocal(this.constant);
        SymbolTable.INSTANCE.addInput(this.constant);
        this.constants.add(this.constant);
        return this;
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public BSVisitor visit(FalseLiteral n) {
        this.name = String.format("%s_%s", CONST, n.f0.toString());
        this.constant = new ConstVariable<Boolean>(this.name, SymbolTable.INSTANCE.getScopeByName(this.getCurrentScope()));
        this.value = "false";
        this.constant.setValue(false);
        this.constant.addTypingConstraint(BOOL);
        this.types.add(ChemTypes.BOOL);
        SymbolTable.INSTANCE.addLocal(this.constant);
        SymbolTable.INSTANCE.addInput(this.constant);
        this.types.add(ChemTypes.BOOL);
        this.constants.add(this.constant);
        return this;
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    @Override
    public BSVisitor visit(Identifier n) {
        this.name = "";
        try {
            Float.parseFloat(n.f0.toString());
            this.name = String.format("%s_%d", REAL, realId++);
        } catch (NumberFormatException e) {
        }

        try {
            Integer.parseInt(n.f0.toString());
            this.name = String.format("%s_%d", INTEGER, integerId++);
        } catch (NumberFormatException e) {
        }

        if (StringUtils.isEmpty(this.name)) {
            if (StringUtils.equalsIgnoreCase("true", n.f0.toString()) ||
                    StringUtils.equalsIgnoreCase("false", n.f0.toString())) {
                this.name = String.format("%s_%d", BOOLEAN, booleanId++);
            } else {
                this.name = n.f0.toString();
            }
        }

        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <AND>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(AndExpression n) {
        n.f0.accept(this);
        this.conditional += this.name;
        this.conditional += "&&";
        n.f2.accept(this);
        this.conditional += this.name;
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <LESSTHAN>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(LessThanExpression n) {
        // TODO: check each side of the conditional for constant or chemical.
        n.f0.accept(this);
        // logger.info(this.name);
        this.conditional += this.name;
        this.conditional += "<";
        n.f2.accept(this);
        this.conditional += SymbolTable.INSTANCE.getCurrentScope().getVariables().get(this.name).getValue();
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <LESSTHANEQUAL>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(LessThanEqualExpression n) {
        n.f0.accept(this);
        this.conditional += this.name;
        this.conditional += "<=";
        n.f2.accept(this);
        this.conditional += this.name;
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <GREATERTHAN>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(GreaterThanExpression n) {
        n.f0.accept(this);
        this.conditional += this.name;
        this.conditional += ">";
        n.f2.accept(this);
        this.conditional += this.name;
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <GREATERTHANEQUAL>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(GreaterThanEqualExpression n) {
        n.f0.accept(this);
        this.conditional += this.name;
        this.conditional += ">=";
        n.f2.accept(this);
        this.conditional += this.name;
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <NOTEQUAL>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(NotEqualExpression n) {
        n.f0.accept(this);
        this.conditional += this.name;
        this.conditional += "!=";
        n.f2.accept(this);
        this.conditional += this.name;
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <OR>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(EqualityExpression n) {
        n.f0.accept(this);
        this.conditional += this.name;
        this.conditional += "==";
        n.f2.accept(this);
        this.conditional += this.name;
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <LESSTHAN>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(OrExpression n) {
        n.f0.accept(this);
        this.conditional += this.name;
        this.conditional += "<";
        n.f2.accept(this);
        this.conditional += this.name;
        return this;
    }

    /**
     * f0 -> <BANG>
     * f1 -> Expression()
     */
    @Override
    public BSVisitor visit(NotExpression n) {
        this.conditional += "!";
        n.f1.accept(this);
        this.conditional += this.name;
        return this;
    }


    /**
     * f0 -> <LPAREN>
     * f1 -> Conditional()
     * f2 -> <RPAREN>
     */
    @Override
    public BSVisitor visit(ConditionalParenthesis n) {
        this.conditional += "(";
        n.f1.accept(this);
        this.conditional += this.name;
        this.conditional += ")";
        return this;
    }

    /**
     * f0 -> <LPAREN>
     * f1 -> MathStatement()
     * f2 -> <RPAREN>
     */
    @Override
    public BSVisitor visit(MathParenthesis n) {
        this.conditional += "(";
        n.f1.accept(this);
        this.conditional += this.name;
        this.conditional += ")";
        return this;
    }

    protected Set<ChemTypes> getTypingConstraints(Variable t) {
        if (BSVisitor.variables.containsKey(t.getScopedName())) {
            return BSVisitor.variables.get(t.getScopedName()).getTypes();
        } else {
            return this.identifier.identifyCompoundForTypes(t.getName());
        }
    }

    /**
     * f0 -> IntegerLiteral()
     * f1 -> ( <SECOND> | <MILLISECOND> | <MICROSECOND> | <HOUR> | <MINUTE> )+
     */
    @Override
    public BSVisitor visit(TimeUnit n) {
        n.f0.accept(this);
        this.units = "SECONDS";
        if (n.f1.present()) {
            if (StringUtils.equalsIgnoreCase(n.f1.toString(), "h")) {
                this.integerLiteral = this.integerLiteral * 3600;
            } else if (StringUtils.equalsIgnoreCase(n.f1.toString(), "m")) {
                this.integerLiteral = this.integerLiteral * 60;
            } else if (StringUtils.equalsIgnoreCase(n.f1.toString(), "us")) {
                this.integerLiteral = this.integerLiteral / 1000000;
            } else if (StringUtils.equalsIgnoreCase(n.f1.toString(), "ms")) {
                this.integerLiteral = this.integerLiteral / 1000;
            } else {
                this.integerLiteral *= 1;
            }
        } else {
            this.units = "SECONDS";
        }
        return this;
    }

    /**
     * f0 -> IntegerLiteral()
     * f1 -> ( <LITRE> | <MILLILITRE> | <MICROLITRE> )+
     */
    @Override
    public BSVisitor visit(VolumeUnit n) {
        n.f0.accept(this);
        if (n.f1.present()) {
            if (StringUtils.equalsIgnoreCase(n.f1.toString(), "L")) {
                this.units = "LITRE";
            } else if (StringUtils.equalsIgnoreCase(n.f1.toString(), "mL")) {
                this.units = "MILLILITRE";
            } else {
                this.units = "MICROLITRE";
            }
        } else {
            this.units = "MICROLITRE";
        }
        return super.visit(n);
    }

    /**
     * f0 -> IntegerLiteral()
     * f1 -> ( <CELSIUS> | <FAHRENHEIT> )+
     */
    @Override
    public BSVisitor visit(TempUnit n) {
        n.f0.accept(this);
        if (n.f1.present()) {
            if (StringUtils.equalsIgnoreCase(n.f1.toString(), "c")) {
                this.units = "CELSIUS";
            } else {
                this.units = "FAHRENHEIT";
            }
        } else {
            this.units = "CELSIUS";
        }
        return super.visit(n);
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
