package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import parser.ast.AssignmentInstruction;
import parser.ast.BranchStatement;
import parser.ast.DetectStatement;
import parser.ast.DrainStatement;
import parser.ast.FalseLiteral;
import parser.ast.FormalParameter;
import parser.ast.FormalParameterList;
import parser.ast.FormalParameterRest;
import parser.ast.Function;
import parser.ast.HeatStatement;
import parser.ast.Identifier;
import parser.ast.Manifest;
import parser.ast.MatLiteral;
import parser.ast.MixStatement;
import parser.ast.NatLiteral;
import parser.ast.RealLiteral;
import parser.ast.RepeatStatement;
import parser.ast.SplitStatement;
import parser.ast.Stationary;
import parser.ast.TrueLiteral;
import parser.visitor.GJNoArguDepthFirst;
import shared.Step;
import symboltable.Branch;
import symboltable.Loop;
import symboltable.Method;
import symboltable.Symbol;
import symboltable.SymbolTable;
import symboltable.Variable;
import typesystem.epa.ChemTypes;

/**
 * @created: 2/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSSymbolTable extends GJNoArguDepthFirst<Step> implements Step {

    public static final Logger logger = LogManager.getLogger(BSSymbolTable.class);

    private SymbolTable symbolTable = new SymbolTable();

    private int scopeId = 0;
    private int integerId = 0;

    //private String scope = DEFAULT_SCOPE;
    // private Variable variable;
    private String name;
    private Set<ChemTypes> types = new HashSet<>();
    private List<Symbol> arguments = new ArrayList<>();
    private static final String REPEAT = "REPEAT";
    private static final String BRANCH = "BRANCH";
    private static final String INTEGER = "INTEGER";


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
     * f0 -> <STATIONARY>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public Step visit(Stationary n) {
        // super.visit(n);
        // Get the types.
        n.f1.accept(this);
        // Get the identifier.
        n.f2.accept(this);
        // Anything in this section is always default scope.
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        return null;
    }

    /**
     * f0 -> <MANIFEST>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public Step visit(Manifest n) {
        // super.visit(n);
        // Get the types.
        n.f1.accept(this);
        // Get the identifier.
        n.f2.accept(this);
        // build the variable now
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        return null;
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     */
    @Override
    public Step visit(AssignmentInstruction n) {
        // super.visit(n.f0);
        // Enumerate the types, if any.
        n.f0.accept(this);
        // Set the identifier.
        n.f1.accept(this);
        // Add the variable to our scope.
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        // Clear the set, we are done with it.
        this.types.clear();
        // Go get the rest of the expression(s).
        n.f3.accept(this);
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
    public Step visit(Function n) {
        // super.visit(n);

        // Get the name of the method.
        n.f1.accept(this);
        // Start a new scope.
        this.symbolTable.newScope(this.name);
        Method symbol = new Method(this.name);

        // Get the parameters of this method
        n.f3.accept(this);
        //this.symbolTable.addLocals(this.arguments);
        symbol.addParameters(this.arguments);
        this.arguments.clear();

        // Get the types of this method.
        n.f5.accept(this);
        symbol.addReturnTypes(this.types);
        this.types.clear();

        // Get the list of statements.
        n.f7.accept(this);
        this.symbolTable.addLocal(symbol);

        // Get the return statement (Currently ignored).
        n.f8.accept(this);

        // Return back to previous scoping.
        this.symbolTable.endScope();
        return null;
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     */
    @Override
    public Step visit(FormalParameter n) {
        // super.visit(n);
        // Go fetch the typing list
        n.f0.accept(this);
        // Go fetch the name
        n.f1.accept(this);
        // save the record.
        Variable v = new Variable(this.name, this.types);
        this.arguments.add(v);
        this.symbolTable.addLocal(v);
        this.types.clear();
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
    public Step visit(RepeatStatement n) {
        // super.visit(n);
        // Start a new scope.
        String name = String.format("%s_%d", REPEAT, scopeId++);
        this.symbolTable.newScope(name);
        Loop symbol = new Loop(name, new HashSet<>());
        this.symbolTable.addLocal(symbol);
        n.f4.accept(this);
        // Return back to old scoping.
        this.symbolTable.endScope();
        return null;
    }

    /**
     * f0 -> <IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE_IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE> <LBRACE> Statement() <RBRACE>
     */
    @Override
    public Step visit(BranchStatement n) {
        // Start a new scope.
        String name = String.format("%s_%d", BRANCH, scopeId++);
        this.symbolTable.newScope(name);
        Branch symbol = new Branch(name, new HashSet<>());
        this.symbolTable.addLocal(symbol);
        n.f0.accept(this);
        // Return back to old scoping.
        this.symbolTable.endScope();
        return null;
    }

    /**
     * f0 -> <MIX>
     * f1 -> PrimaryExpression()
     * f2 -> <WITH>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Step visit(MixStatement n) {
        n.f1.accept(this);
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        n.f3.accept(this);
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        if (n.f4.present()) {
            n.f4.accept(this);
            this.symbolTable.addLocal(new Variable(String.format("%s_%d", INTEGER, integerId++), this.types));
            this.types.clear();
        }
        return null;
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> IntegerLiteral()
     */
    @Override
    public Step visit(SplitStatement n) {
        //super.visit(n);
        n.f1.accept(this);
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        n.f3.accept(this);
        this.symbolTable.addLocal(new Variable(String.format("%s_%d", INTEGER, integerId++), this.types));
        return null;
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    @Override
    public Step visit(DrainStatement n) {
        //super.visit(n);
        n.f1.accept(this);
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        return null;
    }

    /**
     * f0 -> <HEAT>
     * f1 -> PrimaryExpression()
     * f2 -> <AT>
     * f3 -> IntegerLiteral()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Step visit(HeatStatement n) {
        // super.visit(n);

        n.f1.accept(this);
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        n.f3.accept(this);
        this.symbolTable.addLocal(new Variable(String.format("%s_%d", INTEGER, integerId++), this.types));
        this.types.clear();
        if (n.f4.present()) {
            n.f4.accept(this);
            this.symbolTable.addLocal(new Variable(String.format("%s_%d", INTEGER, integerId++), this.types));
            this.types.clear();
        }
        return null;
    }

    /**
     * f0 -> <DETECT>
     * f1 -> PrimaryExpression()
     * f2 -> <ON>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Step visit(DetectStatement n) {
        // super.visit(n);
        n.f1.accept(this);
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        n.f3.accept(this);
        this.symbolTable.addLocal(new Variable(this.name, this.types));
        this.types.clear();
        if (n.f4.present()) {
            n.f4.accept(this);
            this.symbolTable.addLocal(new Variable(String.format("%s_%d", INTEGER, integerId++), this.types));
            this.types.clear();
        }
        return null;
    }

    /**
     * f0 -> <NAT>
     */
    @Override
    public Step visit(NatLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.NAT);
        return null;
    }

    /**
     * f0 -> <MAT>
     */
    @Override
    public Step visit(MatLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.MAT);
        return null;
    }

    /**
     * f0 -> <REAL>
     */
    @Override
    public Step visit(RealLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.REAL);
        return null;
    }

    /**
     * f0 -> <TRUE>
     */
    @Override
    public Step visit(TrueLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.BOOL);
        return null;
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public Step visit(FalseLiteral n) {
        //super.visit(n);
        this.types.add(ChemTypes.BOOL);
        return null;
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    @Override
    public Step visit(Identifier n) {
        this.name = n.f0.toString();
        return null;
    }

    public SymbolTable getSymbolTable() {
        return this.symbolTable;
    }

    public String toString() {
        return this.symbolTable.toString();
    }
}
