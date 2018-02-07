package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import sun.awt.Symbol;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import parser.ast.AssignmentInstruction;
import parser.ast.BSProgram;
import parser.ast.BranchStatement;
import parser.ast.FalseLiteral;
import parser.ast.Function;
import parser.ast.Identifier;
import parser.ast.IntegerLiteral;
import parser.ast.Manifest;
import parser.ast.MatLiteral;
import parser.ast.NatLiteral;
import parser.ast.RealLiteral;
import parser.ast.RepeatStatement;
import parser.ast.Sequence;
import parser.ast.Statement;
import parser.ast.Stationary;
import parser.ast.TrueLiteral;
import parser.ast.Type;
import parser.visitor.GJNoArguDepthFirst;
import phases.inference.rules.Var;
import shared.Step;
import symboltable.Method;
import symboltable.Scope;
import symboltable.Variable;
import typesystem.epa.ChemTypes;

/**
 * @created: 2/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSSymbolTable extends GJNoArguDepthFirst<SymbolTable> implements Step, SymbolTable {

    public static final Logger logger = LogManager.getLogger(BSSymbolTable.class);

    private Map<Scope, Map<String, Variable>> symbolTable = new HashMap<>();

    private int scopeId = 0;

    private Scope scope = new Scope();
    private Variable variable;
    private boolean inAssignment = false;
    private boolean inFunction = false;
    private Method method;
    private String name;
    private Set<ChemTypes> type = new HashSet<>();

    public BSSymbolTable() {

    }

    @Override
    public Step run() {
        return null;
    }

    @Override
    public String getName() {
        return "BSSymbolTable";
    }

    /**
     * f0 -> Function()
     * | Statement()
     */
    @Override
    public SymbolTable visit(Sequence n) {
        // Create the default scoping
        this.scope = new Scope();
        return super.visit(n);
    }

    /**
     * f0 -> ( ( TypingList() )* Identifier() )?
     * f1 -> <ASSIGN>
     * f2 -> Expression()
     */
    @Override
    public SymbolTable visit(AssignmentInstruction n) {
        super.visit(n.f0);
        // Enumerate the types, if any.
        n.f1.accept(this);

        this.variable = new Variable(this.name, this.scope, this.type);
        this.addToScope(this.variable);

        // Clear the set, we are done with it.
        this.type.clear();
        return null;
    }

    /**
     * f0 -> ( <STATIONARY> ( Type() )? PrimaryExpression() )*
     */
    @Override
    public SymbolTable visit(Stationary n) {
        super.visit(n);
        n.f0.accept(this);
        return null;
    }

    /**
     * f0 -> ( <MANIFEST> ( Type() )? PrimaryExpression() )+
     */
    @Override
    public SymbolTable visit(Manifest n) {
        super.visit(n);
        n.f0.accept(this);
        return null;
    }

    /**
     * f0 -> <FUNCTION>
     * f1 -> Identifier()
     * f2 -> <LPAREN>
     * f3 -> ( FormalParameterList() )*
     * f4 -> <RPAREN>
     * f5 -> ( <COLON> TypingList() )?
     * f6 -> <LBRACE>
     * f7 -> ( Statement() )*
     * f8 -> ( <RETURN> Expression() )?
     * f9 -> <RBRACE>
     */
    @Override
    public SymbolTable visit(Function n) {
        super.visit(n);
        // Get the name of the method.
        n.f1.accept(this);
        // Get the type of this method.
        n.f5.accept(this);
        // TODO: Get the parameters of this method
        this.scope = new Scope(this.name);
        return null;
    }

    /**
     * f0 -> <REPEAT>
     * f1 -> IntegerLiteral()
     * f2 -> <TIMES>
     * f3 -> <LBRACE>
     * f4 -> Statement()
     * f5 -> <RBRACE>
     */
    @Override
    public SymbolTable visit(RepeatStatement n) {
        this.scope = new Scope("scope_repeat_" + scopeId++);
        return super.visit(n);
    }

    /**
     * f0 -> <IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE_IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE> <LBRACE> Statement() <RBRACE>
     */
    @Override
    public SymbolTable visit(BranchStatement n) {
        super.visit(n);
        // This is naive right now.
        this.scope = new Scope("scope_branch_" + scopeId++);
        return null;
    }

    /**
     * f0 -> <INTEGER_LITERAL>
     */
    @Override
    public SymbolTable visit(IntegerLiteral n) {
        super.visit(n);
        this.type.add(ChemTypes.NAT);
        return null;
    }

    /**
     * f0 -> <NAT>
     */
    @Override
    public SymbolTable visit(NatLiteral n) {
        super.visit(n);
        this.type.add(ChemTypes.NAT);
        return null;
    }

    /**
     * f0 -> <MAT>
     */
    @Override
    public SymbolTable visit(MatLiteral n) {
        super.visit(n);
        this.type.add(ChemTypes.MAT);
        return null;
    }

    /**
     * f0 -> <REAL>
     */
    @Override
    public SymbolTable visit(RealLiteral n) {
        super.visit(n);
        this.type.add(ChemTypes.REAL);
        return null;
    }

    /**
     * f0 -> <TRUE>
     */
    @Override
    public SymbolTable visit(TrueLiteral n) {
        super.visit(n);
        this.type.add(ChemTypes.BOOL);
        return null;
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public SymbolTable visit(FalseLiteral n) {
        //super.visit(n);
        this.type.add(ChemTypes.BOOL);
        return null;
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    @Override
    public SymbolTable visit(Identifier n) {
        this.name = n.f0.toString();
        return null;
    }

    private void addToScope(Variable v) {
        if (!this.symbolTable.containsKey(this.scope)) {
            this.symbolTable.put(this.scope, new HashMap<>());
        }

        this.symbolTable.get(this.scope).put(v.getName(), v);
    }


    public Map<Scope, Map<String, Variable>> getSymbolTable() {
        return this.symbolTable;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();

        for (Map.Entry<Scope, Map<String, Variable>> entry : this.symbolTable.entrySet()) {
            sb.append("Scope: ").append(entry.getKey()).append(System.lineSeparator());
            for (Map.Entry<String, Variable> vars : entry.getValue().entrySet()) {
                sb.append("\t").append(vars.getValue()).append(System.lineSeparator());
            }
            sb.append("==============").append(System.lineSeparator());
        }

        return sb.toString();
    }
}
