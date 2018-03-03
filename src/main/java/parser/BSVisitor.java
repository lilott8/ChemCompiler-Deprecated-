package parser;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jgrapht.graph.AbstractBaseGraph;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import chemical.epa.ChemTypes;
import chemical.identification.IdentifierFactory;
import ir.soot.Body;
import ir.soot.instruction.Instruction;
import ir.soot.statement.Block;
import ir.soot.statement.Statement;
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
    protected int scopeId = 0;
    protected int realId = 0;
    protected int booleanId = 0;
    protected int integerId = 0;

    protected SymbolTable symbolTable = new SymbolTable();

    private Deque<String> scope = new ArrayDeque<>();

    public static final Logger logger = LogManager.getLogger(BSVisitor.class);

    // Keep track of the instruction id to input/outputs
    protected static Map<Integer, Instruction> instructions = new LinkedHashMap<>();
    protected static Map<String, Variable> variables = new HashMap<>();
    protected Map<String, Instruction> controlInstructions = new HashMap<>();

    protected boolean assignToFunction = false;
    // Allows us to handle nested branching and if/elseif/.../else.
    protected Deque<Instruction> branchStack = new ArrayDeque<>();
    // Allows us to handle nested looping.
    protected Deque<Instruction> loopStack = new ArrayDeque<>();

    // Current instruction to work on.
    protected Instruction instruction;
    // Current name to work on.
    protected String name;
    // Current type(s) of variables.
    protected Set<ChemTypes> types = new HashSet<>();
    // Current method to work on.
    protected Method method;

    // Ability to identify stuff.
    protected chemical.identification.Identifier identifier = IdentifierFactory.getIdentifier();

    {
        this.newScope(SymbolTable.DEFAULT_SCOPE);
    }

    public BSVisitor() { }

    public BSVisitor(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    public SymbolTable getSymbolTable() {
        return this.symbolTable;
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
                logger.warn(String.format("%s is equal to %s", t, variables.get(t.getName())));
            }
        }
    }

    protected void addInstruction(Instruction i) {
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
        this.name = String.format("%s_%d", INTEGER, integerId++);
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
        this.types.add(ChemTypes.BOOL);
        return this;
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public BSVisitor visit(FalseLiteral n) {
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
        return this;
    }

    protected Set<ChemTypes> getTypingConstraints(Variable t) {
        if (BSVisitor.variables.containsKey(t.getScopedName())) {
            return BSVisitor.variables.get(t.getScopedName()).getTypes();
        } else {
            return this.identifier.identifyCompoundForTypes(t.getName());
        }
    }
}
