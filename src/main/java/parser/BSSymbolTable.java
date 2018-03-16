package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;
import ir.Invoke;
import ir.InvokeStatement;
import parser.ast.AssignmentInstruction;
import parser.ast.BranchStatement;
import parser.ast.DetectStatement;
import parser.ast.DrainStatement;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
import parser.ast.FormalParameter;
import parser.ast.Function;
import parser.ast.FunctionInvoke;
import parser.ast.HeatStatement;
import parser.ast.Manifest;
import parser.ast.MixStatement;
import parser.ast.Module;
import parser.ast.RepeatStatement;
import parser.ast.SplitStatement;
import parser.ast.Stationary;
import shared.variable.AssignedVariable;
import shared.variable.DefinedVariable;
import shared.variable.Method;
import shared.variable.Property;
import shared.variable.SensorVariable;
import shared.variable.StationaryVariable;
import shared.variable.Variable;
import symboltable.SymbolTable;

import static chemical.epa.ChemTypes.MODULE;
import static chemical.epa.ChemTypes.NAT;

/**
 * @created: 2/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSSymbolTable extends BSVisitor {

    public static final Logger logger = LogManager.getLogger(BSSymbolTable.class);
    // Arguments to functions, etc.
    private List<Variable> arguments = new ArrayList<>();

    public BSSymbolTable() {
    }

    @Override
    public BSVisitor run() {
        return this;
    }

    @Override
    public String getName() {
        return this.getClass().getName();
    }

    /**
     * f0 -> <MODULE>
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(Module n) {
        // Get the name.
        n.f1.accept(this);
        // Build the symbol.
        Variable f1 = new SensorVariable(this.name, this.symbolTable.getCurrentScope());
        f1.addTypingConstraint(MODULE);
        addVariable(f1);
        this.symbolTable.addInput(f1);
        // Add the symbol to the scope.
        this.symbolTable.addLocal(f1);

        return this;
    }

    /**
     * f0 -> <STATIONARY>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Stationary n) {
        // super.visit(n);
        // Get the types.
        n.f1.accept(this);
        // Get the identifier.
        n.f2.accept(this);

        // Type checking material.
        Variable f2 = new StationaryVariable(this.name);
        f2.addScope(this.symbolTable.getCurrentScope());
        f2.addTypingConstraints(this.getTypingConstraints(f2));
        this.symbolTable.addLocal(f2);
        this.symbolTable.addInput(f2);
        addVariable(f2);
        // End type checking.

        // Anything in this section is always default scope.
        this.symbolTable.addLocal(f2);
        this.types.clear();
        return this;
    }

    /**
     * f0 -> <MANIFEST>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Manifest n) {
        // super.visit(n);
        // Begin type checking.

        // Get the types.
        n.f1.accept(this);
        // Get the identifier.
        n.f2.accept(this);

        // Build the symbol.
        Variable f2 = new DefinedVariable(this.name);
        f2.addScope(this.symbolTable.getCurrentScope());
        f2.addTypingConstraints(this.getTypingConstraints(f2));
        addVariable(f2);
        // End type checking.

        // build the variable now
        this.symbolTable.addLocal(f2);
        this.symbolTable.addInput(f2);
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
    public BSVisitor visit(AssignmentInstruction n) {
        // Get the expression done before we get the identifier.
        // That way we can set the appropriate instruction.
        n.f3.accept(this);
        // Once we have established the expression,
        // We can identify the identifier.
        n.f1.accept(this);
        // Search the hierarchy for the output var.
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name, this.symbolTable.getCurrentScope());
        if (f1 == null) {
            f1 = new AssignedVariable(this.name, this.symbolTable.getCurrentScope());
            if (n.f0.present()) {
                n.f0.accept(this);
                f1.addTypingConstraints(this.getTypingConstraints(f1));
            }
            this.symbolTable.addLocal(f1);
        }

        if (this.instruction instanceof Invoke) {
            f1.addTypingConstraints(this.method.getTypes());
        } else {
            f1.addTypingConstraints(this.getTypingConstraints(f1));
        }
        addVariable(f1);
        this.types.clear();
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
        // Get the method name.
        n.f0.accept(this);
        // Get the method.
        Method method = this.symbolTable.getMethods().get(this.name);
        if (method == null) {
            logger.fatal("Undeclared function: " + this.name);
            return this;
        }

        this.instruction = new InvokeStatement(method);
        n.f2.accept(this);
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
    public BSVisitor visit(Function n) {
        // Lets us know if we have a typed function,
        // If we do, then there must be a return statement.
        boolean needReturn = false;
        // Get the name of the method.
        n.f1.accept(this);
        // The method belongs to the parent scope.
        // Variable f1 = new AssignedVariable(this.name, this.symbolTable.getCurrentScope());
        // Now we have a new scope
        this.symbolTable.newScope(this.name);
        // Start a new scope.
        this.method = new Method(this.name);

        // Get the parameters of this method
        n.f3.accept(this);
        // Add the parameters to the method.
        // Parameters are not local to the method.
        this.method.addParameters(this.arguments);
        // Clear the arguments list
        this.arguments.clear();

        // Get the type(s) of this method.
        if (n.f5.present()) {
            n.f5.accept(this);
            this.method.addReturnTypes(this.types);
            this.types.clear();
            needReturn = true;
        } else {
            this.types.add(ChemTypes.NULL);
            this.method.addReturnTypes(this.types);
            this.types.clear();
        }

        // Get the list of statements.
        n.f7.accept(this);

        if (n.f8.present()) {
            // Get the return statement.
            n.f8.accept(this);
            // If this symbol has already been processed, we don't have to do anything.
            // If there is a return type, then we must add that to the variable name.
            if (!BSVisitor.variables.containsKey(this.symbolTable.getCurrentScope().getName() + "_" + this.name)) {
                Variable ret = checkForOrCreateVariable(); // new Variable(this.name, this.symbolTable.getCurrentScope());
                ret.addTypingConstraints(method.getTypes());
                this.symbolTable.addLocal(ret);
                addVariable(ret);
            }

            // This will associate the type of the function with the type of what is being returned.
            if (!method.hasReturnTypes()) {
                method.addReturnTypes(BSVisitor.variables.get(this.symbolTable.getCurrentScope().getName() + "_" + this.name).getTypes());
            }
        } else {
            if (needReturn) {
                logger.fatal("You need a return statement!");
            }
        }

        this.symbolTable.addMethod(this.method);
        // addVariable(f1);

        this.symbolTable.endScope();
        // Remove the lock for functions.

        return this;
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(FormalParameter n) {
        // super.visit(n);
        // Go fetch the typing list
        n.f0.accept(this);
        // Go fetch the name
        n.f1.accept(this);
        // save the record.
        Variable f1 = new AssignedVariable(this.name, this.types, this.symbolTable.getCurrentScope());
        // this.arguments.add(v);
        this.symbolTable.addLocal(f1);

        this.arguments.add(f1);

        this.types.clear();

        return this;
    }

    /**
     * f0 -> <REPEAT>
     * f1 -> IntegerLiteral()
     * f2 -> <TIMES>
     * f3 -> <LBRACE>
     * f4 -> ( Statement() )+
     * f5 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(RepeatStatement n) {
        // super.visit(n);
        // Start a new scope.
        String scopeName = String.format("%s_%d", REPEAT, this.getNextScopeId());
        this.symbolTable.newScope(scopeName);

        n.f1.accept(this);
        Variable f1 = new AssignedVariable<Integer>(this.name, this.symbolTable.getCurrentScope());
        f1.setValue(Integer.parseInt(this.value));
        f1.addTypingConstraint(NAT);
        addVariable(f1);
        this.symbolTable.addLocal(f1);

        // Get the statements.
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
     * f5 -> ( Statement() )+
     * f6 -> <RBRACE>
     * f7 -> ( ElseIfStatement() )*
     * f8 -> ( ElseStatement() )?
     */
    @Override
    public BSVisitor visit(BranchStatement n) {
        // Build the instruction.
        logger.fatal("You need to reset the instruction in If");
        // Build the name.
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        // Create a new scope.
        this.symbolTable.newScope(scopeName);
        // Build the variable that resolves a branch evaluation.
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());
        Variable term = new AssignedVariable(this.name, this.symbolTable.getCurrentScope());
        term.addTypingConstraint(NAT);
        addVariable(term);
        // End type checking.

        this.symbolTable.addLocal(term);
        // Get the expression.
        n.f2.accept(this);
        // Get the statement.
        n.f5.accept(this);
        // Return back to old scoping.
        this.symbolTable.endScope();

        if (n.f7.present()) {
            n.f7.accept(this);
        }

        if (n.f8.present()) {
            n.f8.accept(this);
        }

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
        // super.visit(n);
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        this.symbolTable.newScope(scopeName);

        // Begin type checking.
        logger.fatal("You need to reset the instruction in ElseIf");
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());
        logger.warn(String.format("Symbol Table elseif: %s_%s", this.symbolTable.getCurrentScope().getName(), this.name));
        Variable term = new AssignedVariable(this.name, this.symbolTable.getCurrentScope());
        term.addTypingConstraint(NAT);
        addVariable(term);
        // End type checking.

        this.symbolTable.addLocal(term);
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
    public BSVisitor visit(ElseStatement n) {
        // super.visit(n);
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        this.symbolTable.newScope(scopeName);
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
    public BSVisitor visit(MixStatement n) {
        // Get the first material.
        n.f1.accept(this);
        checkForOrCreateVariable();

        // Get the other material.
        n.f3.accept(this);
        checkForOrCreateVariable();

        if (n.f4.present()) {
            n.f4.accept(this);
            this.checkForOrCreateProperty("SECONDS");
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
    public BSVisitor visit(SplitStatement n) {
        //super.visit(n);
        n.f1.accept(this);
        checkForOrCreateVariable();

        n.f3.accept(this);
        // Use the generated name for the integer.
        Property f3 = new Property<Integer>(this.name, this.symbolTable.getCurrentScope());
        f3.setValue(this.value);
        f3.addTypingConstraint(NAT);
        addVariable(f3);
        this.symbolTable.addLocal(f3);

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
    public BSVisitor visit(DetectStatement n) {
        // super.visit(n);
        // Get the name
        n.f1.accept(this);
        this.checkForOrCreateVariable();

        n.f3.accept(this);
        this.checkForOrCreateVariable();

        if (n.f4.present()) {
            n.f4.accept(this);
            this.checkForOrCreateProperty("SECONDS");
        }

        return this;
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(DrainStatement n) {
        //super.visit(n);
        n.f1.accept(this);
        Variable term = this.checkForOrCreateVariable();

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
    public BSVisitor visit(HeatStatement n) {
        // super.visit(n);

        n.f1.accept(this);
        this.checkForOrCreateVariable();

        n.f3.accept(this);
        this.checkForOrCreateProperty("CELSIUS");

        if (n.f4.present()) {
            n.f4.accept(this);
            this.checkForOrCreateProperty("SECONDS");

        }
        return this;
    }


    private Variable checkForOrCreateVariable() {
        return checkForOrCreateVariable(new HashSet<>());
    }

    private Property checkForOrCreateProperty(String units) {
        Property prop = (Property) this.symbolTable.searchScopeHierarchy(this.name, this.symbolTable.getCurrentScope());
        if (prop == null) {
            prop = (Property) this.constant;
            // Set<ChemTypes> types = new HashSet<>();
            // types.add(REAL);
            // prop = new Property(this.name, types, this.symbolTable.getCurrentScope());
            prop.setValue(Integer.parseInt(this.value));
            prop.setUnits(units);
            addVariable(prop);
            this.symbolTable.addLocal(prop);
        }
        this.types.clear();
        return prop;
    }

    private Variable checkForOrCreateVariable(Set<ChemTypes> inputTypes) {
        Variable declaration = this.symbolTable.searchScopeHierarchy(this.name, this.symbolTable.getCurrentScope());
        if (declaration == null) {
            declaration = new AssignedVariable(this.name, this.symbolTable.getCurrentScope());
            if (inputTypes.isEmpty()) {
                declaration.addTypingConstraints(this.getTypingConstraints(declaration));
            } else {
                declaration.addTypingConstraints(inputTypes);
            }
            addVariable(declaration);
            this.symbolTable.addLocal(declaration);
        }
        this.types.clear();
        return declaration;
    }


    public SymbolTable getSymbolTable() {
        return this.symbolTable;
    }

    public String toString() {
        return this.symbolTable.toString();
        //return BSVisitor.statements.toString();
    }


}
