package parser;

import java.util.ArrayDeque;
import java.util.Deque;

import ir.Experiment;
import parser.ast.Assignment;
import parser.ast.BSProgram;
import parser.ast.DetectInstruction;
import parser.ast.DrainInstruction;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
import parser.ast.FalseLiteral;
import parser.ast.FunctionDefinition;
import parser.ast.FunctionInvoke;
import parser.ast.HeatInstruction;
import parser.ast.Identifier;
import parser.ast.IfStatement;
import parser.ast.IntegerLiteral;
import parser.ast.Manifest;
import parser.ast.MatLiteral;
import parser.ast.MixInstruction;
import parser.ast.Module;
import parser.ast.NatLiteral;
import parser.ast.RealLiteral;
import parser.ast.RepeatInstruction;
import parser.ast.SplitInstruction;
import parser.ast.Stationary;
import parser.ast.TrueLiteral;
import parser.visitor.GJNoArguDepthFirst;
import shared.variable.Method;
import shared.variable.Variable;
import symboltable.SymbolTable;
import typesystem.elements.Formula;
import typesystem.rules.Rule;

import static chemical.epa.ChemTypes.NAT;

/**
 * @created: 2/14/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSIRConverter extends BSVisitor {

    private Experiment experiment = new Experiment(1, "Experiment");

    public BSIRConverter(SymbolTable symbolTable) {
        super(symbolTable);
    }

    @Override
    public BSVisitor run() {
        return null;
    }

    @Override
    public String getName() {
        return BSIRConverter.class.getName();
    }

    /**
     * f0 -> <MODULE>
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(Module n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = variables.get(this.scopifyName());

        // Build the IR data structure.
        this.experiment.addModule(f1);

        return this;
    }

    /**
     * f0 -> <STATIONARY>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Stationary n) {
        // Get the name.
        n.f2.accept(this);
        Variable f2 = variables.get(this.scopifyName());

        // Build the IR data structure.
        this.experiment.addStationary(f2);

        return this;
    }

    /**
     * f0 -> <MANIFEST>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Manifest n) {
        // Get the name.
        n.f2.accept(this);
        Variable f2 = variables.get(this.scopifyName());

        // Build the IR data structure.
        this.experiment.addManifest(f2);

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
    public BSVisitor visit(FunctionDefinition n) {
        // super.visit(n);
        // Get the name of the method.
        n.f1.accept(this);
        // Get a new scope.
        this.newScope(this.name);
        // Build the method.
        this.method = this.symbolTable.getMethods().get(this.name);

        // Add the method.
        this.experiment.addMethods(this.method);

        this.endScope();
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
    public BSVisitor visit(IfStatement n) {
        // Build the name.
        this.name = String.format("%s_%d", BRANCH, scopeId++);
        // Create a new scope.
        this.newScope(this.name);
        // Get the expression.
        n.f2.accept(this);
        Variable f2 = variables.get(this.scopifyName());

        // Get the statement.
        n.f5.accept(this);

        // Return back to old scoping.
        this.endScope();

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
    public BSVisitor visit(ElseIfStatement n) {
        // Get the name and scope.
        String scopeName = String.format("%s_%d", BRANCH, scopeId++);
        this.newScope(scopeName);

        // Get the expression.
        n.f2.accept(this);

        // Get the statements in the scope.
        n.f5.accept(this);
        // Return back to old scoping.
        this.endScope();
        return this;
    }

    /**
     * f0 -> <ELSE>
     * f1 -> <LBRACE>
     * f2 -> Statement()
     * f3 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(ElseStatement n) {
        // super.visit(n);
        String scopeName = String.format("%s_%d", BRANCH, scopeId++);
        this.newScope(scopeName);
        n.f2.accept(this);

        // Return back to old scoping.

        this.endScope();
        return this;
    }

    /**
     * f0 -> ( TypingList() )?
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     */
    @Override
    public BSVisitor visit(Assignment n) {
        // super.visit(n);
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
    public BSVisitor visit(MixInstruction n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = variables.get(this.scopifyName());
        n.f3.accept(this);
        Variable f3 = variables.get(this.scopifyName());

        // Build the IR data structure.

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = variables.get(this.scopifyName());
            // Add f4 to the data structure.
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
    public BSVisitor visit(SplitInstruction n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = variables.get(this.scopifyName());
        // Get the name.
        n.f3.accept(this);
        Variable f3 = variables.get(this.scopifyName());

        // Build the IR data structure.

        return this;
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(DrainInstruction n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = variables.get(this.scopifyName());

        // Build the IR data structure.

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
    public BSVisitor visit(HeatInstruction n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = variables.get(this.scopifyName());
        // Get the name.
        n.f3.accept(this);
        Variable f3 = variables.get(this.scopifyName());

        // Build the IR data structure.

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = variables.get(this.scopifyName());
            // Add f4 to the data structure.
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
    public BSVisitor visit(DetectInstruction n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = variables.get(this.scopifyName());
        n.f3.accept(this);
        Variable f3 = variables.get(this.scopifyName());

        // Build the IR data structure.

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = variables.get(this.scopifyName());
            // Add f4 to the data structure.
        }


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
    public BSVisitor visit(RepeatInstruction n) {
        // super.visit(n);
        String scopeName = String.format("%s_%d", REPEAT, scopeId++);
        this.newScope(this.name);
        this.name = String.format("%s_%d", NAT, integerId++);

        // Build the new IR data structure.

        this.endScope();
        return this;
    }

    /**
     * f0 -> Identifier()
     * f1 -> <LPAREN>
     * f2 -> ( ExpressionList() )?
     * f3 -> <RPAREN>
     */
    @Override
    public BSVisitor visit(FunctionInvoke n) {
        // super.visit(n);
        return this;
    }

    public String toString() {
        return this.experiment.toString();
    }
}