package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import parser.ast.Assignment;
import parser.ast.DetectInstruction;
import parser.ast.DrainInstruction;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
import parser.ast.FalseLiteral;
import parser.ast.FormalParameter;
import parser.ast.FunctionDefinition;
import parser.ast.HeatInstruction;
import parser.ast.Identifier;
import parser.ast.IfStatement;
import parser.ast.Manifest;
import parser.ast.MatLiteral;
import parser.ast.MixInstruction;
import parser.ast.NatLiteral;
import parser.ast.RealLiteral;
import parser.ast.RepeatInstruction;
import parser.ast.SplitInstruction;
import parser.ast.Stationary;
import parser.ast.TrueLiteral;
import parser.visitor.GJNoArguDepthFirst;
import shared.Step;
import shared.variables.Symbol;
import symboltable.Method;
import symboltable.SymbolTable;
import chemical.epa.ChemTypes;

/**
 * @created: 2/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSSymbolTable extends GJNoArguDepthFirst<Step> implements Step {

    public static final Logger logger = LogManager.getLogger(BSSymbolTable.class);
    private static final String REPEAT = "REPEAT";
    private static final String BRANCH = "BRANCH";
    private static final String INTEGER = "INTEGER";
    private SymbolTable symbolTable = new SymbolTable();
    private int scopeId = 0;
    private int integerId = 0;
    //private String scope = DEFAULT_SCOPE;
    // private Variable variable;
    private String name;
    private Set<ChemTypes> types = new HashSet<>();
    private List<Symbol> arguments = new ArrayList<>();


    public BSSymbolTable() {
    }

    @Override
    public Step run() {
        return this;
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
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        return this;
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
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        return this;
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     */
    @Override
    public Step visit(Assignment n) {
        // super.visit(n.f0);
        // Enumerate the types, if any.
        n.f0.accept(this);
        // Set the identifier.
        n.f1.accept(this);
        // Add the variable to our scope.
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        // Clear the set, we are done with it.
        this.types.clear();
        // Go get the rest of the expression(s).
        n.f3.accept(this);
        return this;
    }

    /**
     * f0 -> <FUNCTION>
     * f1 -> Identifier()
     * f2 -> <LPAREN>
     * f3 -> ( FormalParameterList() )*
     * f4 -> <RPAREN>
     * f5 -> ( <COLON> TypingList() )?
     * f6 -> <LBRACE>
     * f7 -> ( Statement() )+
     * f8 -> ( <RETURN> Expression() )?
     * f9 -> <RBRACE>
     */
    @Override
    public Step visit(FunctionDefinition n) {
        // super.visit(n);

        // Get the name of the method.
        n.f1.accept(this);
        // Start a new scope.
        this.symbolTable.newScope(this.name);
        Method method = new Method(this.name);

        // Get the parameters of this method
        n.f3.accept(this);
        // Add the parameters to the method.
        method.addParameters(this.arguments);
        // Clear the arguments list
        this.arguments.clear();

        // Get the types of this method.
        if (n.f5.present()) {
            n.f5.accept(this);
            method.addReturnTypes(this.types);
            this.types.clear();
        } else {
            this.types.add(ChemTypes.NULL);
            method.addReturnTypes(this.types);
            this.types.clear();
        }
        this.symbolTable.addMethod(method);

        // Get the list of statements.
        n.f7.accept(this);
        // this.symbolTable.addLocal(symbol);

        if (n.f8.present()) {
            // Get the return statement (Currently ignored).
            n.f8.accept(this);
        }

        // Return back to previous scoping.
        this.symbolTable.endScope();
        return this;
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
        Symbol v = new Symbol(this.name, this.types);
        // this.arguments.add(v);
        this.symbolTable.addLocal(v);
        this.types.clear();
        return this;
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
    public Step visit(RepeatInstruction n) {
        // super.visit(n);
        // Start a new scope.
        String name = String.format("%s_%d", REPEAT, scopeId++);
        this.symbolTable.newScope(name);
        Set<ChemTypes> types = new HashSet<>();
        types.add(ChemTypes.NAT);
        this.symbolTable.addLocal(new Symbol(String.format("%s_%d", INTEGER, integerId), types));
        types = null;
        //Loop symbol = new Loop(name, new HashSet<>());
        //this.symbolTable.addLocal(symbol);
        n.f4.accept(this);
        // Return back to old scoping.
        this.symbolTable.endScope();
        return this;
    }

    /**
     * f0 -> <IF>
     * f1 -> <LPAREN>
     * f2 -> Expression()
     * f3 -> <RPAREN>
     * f4 -> <LBRACE>
     * f5 -> Statement()
     * f6 -> <RBRACE>
     */
    @Override
    public Step visit(IfStatement n) {
        // super.visit(n);
        // String name = String.format("%s_%d", BRANCH, scopeId++);
        this.symbolTable.newScope(name);
        // Branch symbol = new Branch(name, new HashSet<>());
        n.f2.accept(this);
        // this.symbolTable.addLocal(symbol);
        n.f5.accept(this);
        // Return back to old scoping.
        this.symbolTable.endScope();

        return this;
    }

    /**
     * f0 -> <ELSE_IF>
     * f1 -> <LPAREN>
     * f2 -> Expression()
     * f3 -> <RPAREN>
     * f4 -> <LBRACE>
     * f5 -> Statement()
     * f6 -> <RBRACE>
     */
    @Override
    public Step visit(ElseIfStatement n) {
        // super.visit(n);
        // String name = String.format("%s_%d", BRANCH, scopeId++);
        this.symbolTable.newScope(name);
        // Branch symbol = new Branch(name, new HashSet<>());
        // this.symbolTable.addLocal(symbol);
        n.f2.accept(this);
        n.f5.accept(this);
        // Return back to old scoping.
        this.symbolTable.endScope();

        return this;
    }

    /**
     * f0 -> <ELSE>
     * f1 -> <LBRACE>
     * f2 -> Statement()
     * f3 -> <RBRACE>
     */
    @Override
    public Step visit(ElseStatement n) {
        // super.visit(n);
        String name = String.format("%s_%d", BRANCH, scopeId++);
        this.symbolTable.newScope(name);
        n.f2.accept(this);
        // Return back to old scoping.
        this.symbolTable.endScope();

        return this;
    }

    /**
     * f0 -> <MIX>
     * f1 -> PrimaryExpression()
     * f2 -> <WITH>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Step visit(MixInstruction n) {
        n.f1.accept(this);
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        n.f3.accept(this);
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        if (n.f4.present()) {
            n.f4.accept(this);
            this.symbolTable.addLocal(new Symbol(String.format("%s_%d", INTEGER, integerId++), this.types));
            this.types.clear();
        }
        return this;
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> IntegerLiteral()
     */
    @Override
    public Step visit(SplitInstruction n) {
        //super.visit(n);
        n.f1.accept(this);
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        n.f3.accept(this);
        this.symbolTable.addLocal(new Symbol(String.format("%s_%d", INTEGER, integerId++), this.types));
        return this;
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    @Override
    public Step visit(DrainInstruction n) {
        //super.visit(n);
        n.f1.accept(this);
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        return this;
    }

    /**
     * f0 -> <HEAT>
     * f1 -> PrimaryExpression()
     * f2 -> <AT>
     * f3 -> IntegerLiteral()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Step visit(HeatInstruction n) {
        // super.visit(n);

        n.f1.accept(this);
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        n.f3.accept(this);
        this.symbolTable.addLocal(new Symbol(String.format("%s_%d", INTEGER, integerId++), this.types));
        this.types.clear();
        if (n.f4.present()) {
            n.f4.accept(this);
            this.symbolTable.addLocal(new Symbol(String.format("%s_%d", INTEGER, integerId++), this.types));
            this.types.clear();
        }
        return this;
    }

    /**
     * f0 -> <DETECT>
     * f1 -> PrimaryExpression()
     * f2 -> <ON>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Step visit(DetectInstruction n) {
        // super.visit(n);
        n.f1.accept(this);
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        n.f3.accept(this);
        this.symbolTable.addLocal(new Symbol(this.name, this.types));
        this.types.clear();
        if (n.f4.present()) {
            n.f4.accept(this);
            this.symbolTable.addLocal(new Symbol(String.format("%s_%d", INTEGER, integerId++), this.types));
            this.types.clear();
        }
        return this;
    }

    /**
     * f0 -> <NAT>
     */
    @Override
    public Step visit(NatLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.NAT);
        return this;
    }

    /**
     * f0 -> <MAT>
     */
    @Override
    public Step visit(MatLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.MAT);
        return this;
    }

    /**
     * f0 -> <REAL>
     */
    @Override
    public Step visit(RealLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.REAL);
        return this;
    }

    /**
     * f0 -> <TRUE>
     */
    @Override
    public Step visit(TrueLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.BOOL);
        return this;
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public Step visit(FalseLiteral n) {
        //super.visit(n);
        this.types.add(ChemTypes.BOOL);
        return this;
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    @Override
    public Step visit(Identifier n) {
        this.name = n.f0.toString();
        return this;
    }

    public SymbolTable getSymbolTable() {
        return this.symbolTable;
    }

    public String toString() {
        return this.symbolTable.toString();
    }
}
