package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chemical.epa.ChemTypes;
import compilation.symboltable.UsageGovernor;
import ir.Invoke;
import ir.InvokeStatement;
import parser.ast.AssignmentStatement;
import parser.ast.BranchStatement;
import parser.ast.Conditional;
import parser.ast.DetectStatement;
import parser.ast.DispenseStatement;
import parser.ast.DrainStatement;
import parser.ast.ElseBranchStatement;
import parser.ast.ElseIfBranchStatement;
import parser.ast.FormalParameter;
import parser.ast.FormalParameterList;
import parser.ast.FormalParameterRest;
import parser.ast.FunctionDefinition;
import parser.ast.FunctionInvoke;
import parser.ast.HeatStatement;
import parser.ast.Manifest;
import parser.ast.MinusExpression;
import parser.ast.MixStatement;
import parser.ast.Module;
import parser.ast.PlusExpression;
import parser.ast.RepeatStatement;
import parser.ast.SplitStatement;
import parser.ast.Stationary;
import parser.ast.TimesExpression;
import parser.ast.WhileStatement;
import shared.errors.InvalidSyntaxException;
import shared.properties.Volume;
import shared.variable.NamedVariable;
import shared.variable.ManifestVariable;
import shared.variable.Method;
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
    private int id = 0;
    // Arguments to functions, etc.
    private List<Variable> arguments = new ArrayList<>();
    private String unit = "";

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
        Variable f1 = new SensorVariable(this.name, SymbolTable.INSTANCE.getCurrentScope());
        f1.addTypingConstraint(MODULE);
        addVariable(f1);
        SymbolTable.INSTANCE.addInput(f1);
        // Add the symbol to the scope.
        SymbolTable.INSTANCE.addLocal(f1);
        SymbolTable.INSTANCE.addConstant(f1);
        UsageGovernor.defVar(f1.getName());
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
        f2.addScope(SymbolTable.INSTANCE.getCurrentScope());
        f2.addTypingConstraints(this.getTypingConstraints(f2));
        f2.setProperty(new Volume("unknown", "L", 10000));
        SymbolTable.INSTANCE.addLocal(f2);
        SymbolTable.INSTANCE.addInput(f2);
        addVariable(f2);
        // End type checking.

        // Anything in this section is always default scope.
        SymbolTable.INSTANCE.addLocal(f2);
        SymbolTable.INSTANCE.addConstant(f2);
        UsageGovernor.defVar(f2.getName());
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
        Variable f2 = new ManifestVariable(this.name);
        f2.addScope(SymbolTable.INSTANCE.getCurrentScope());
        f2.addTypingConstraints(this.getTypingConstraints(f2));
        f2.setProperty(new Volume("unknown", "L", 10000));
        addVariable(f2);
        // End type checking.

        // build the variable now
        SymbolTable.INSTANCE.addLocal(f2);
        SymbolTable.INSTANCE.addInput(f2);
        SymbolTable.INSTANCE.addConstant(f2);
        UsageGovernor.defVar(f2.getName());
        this.types.clear();

        return this;
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> RightOp()
     */
    @Override
    public BSVisitor visit(AssignmentStatement n) {
        // Once we have established the expression,
        // We can identify the identifier.
        n.f1.accept(this);
        // Search the hierarchy for the output var.
        Variable f1 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, SymbolTable.INSTANCE.getCurrentScope());
        if (f1 == null) {
            f1 = new NamedVariable(this.name, SymbolTable.INSTANCE.getCurrentScope());
            if (n.f0.present()) {
                n.f0.accept(this);
                f1.addTypingConstraints(this.getTypingConstraints(f1));
            }
        }

        if (this.instruction instanceof Invoke) {
            f1.addTypingConstraints(this.method.getTypes());
        } else {
            f1.addTypingConstraints(this.getTypingConstraints(f1));
        }
        this.assignTo = f1;
        addVariable(f1);
        SymbolTable.INSTANCE.addLocal(f1);
        this.types.clear();

        // Get the expression done before we get the identifier.
        // That way we can set the appropriate instruction.
        n.f3.accept(this);
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
        Method method = SymbolTable.INSTANCE.getMethods().get(this.name);
        if (method == null) {
            throw new InvalidSyntaxException("Function: " + this.name + " is undeclared.");
            // return this;
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
    public BSVisitor visit(FunctionDefinition n) {
        // Lets us know if we have a typed function,
        // If we do, then there must be a return statement.
        boolean needReturn = false;
        // Get the name of the method.
        n.f1.accept(this);
        // The method belongs to the parent scope.
        // Variable f1 = new NamedVariable(this.name, SymbolTable.INSTANCE.getCurrentScope());
        // Now we have a new scope
        SymbolTable.INSTANCE.newScope(this.name);
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
            needReturn = true;
        }
        this.types.clear();

        // Get the list of statements.
        n.f7.accept(this);

        if (n.f8.present()) {
            // Get the return statement.
            n.f8.accept(this);
            // If this symbol has already been processed, we don't have to do anything.
            // If there is a return type, then we must add that to the variable name.
            if (SymbolTable.INSTANCE.searchScopeHierarchy(this.name, SymbolTable.INSTANCE.getCurrentScope()) == null) {
                Variable ret = checkForOrCreateVariable();
                ret.addTypingConstraints(method.getTypes());
                SymbolTable.INSTANCE.addLocal(ret);
                addVariable(ret);
            }

            // This will associate the type of the function with the type of what is being returned.
            if (!method.hasReturnTypes()) {
                method.addReturnTypes(SymbolTable.INSTANCE.searchScopeHierarchy(this.name, SymbolTable.INSTANCE.getCurrentScope()).getTypes());
            }
        } else {
            if (needReturn) {
                logger.fatal("You need a return statement!");
            }
            throw new IllegalStateException("You must include a return statement for a function.");
        }

        SymbolTable.INSTANCE.addMethod(this.method);
        // addVariable(f1);

        SymbolTable.INSTANCE.endScope();
        // Remove the lock for functions.

        return this;
    }

    /**
     * f0 -> FormalParameter()
     * f1 -> ( FormalParameterRest() )*
     */
    @Override
    public BSVisitor visit(FormalParameterList n) {
        n.f0.accept(this);

        if (n.f1.present()) {
            n.f1.accept(this);
        }
        return this;
    }

    /**
     * f0 -> <COMMA>
     * f1 -> FormalParameter()
     */
    @Override
    public BSVisitor visit(FormalParameterRest n) {
        n.f1.accept(this);
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
        Variable f1 = new NamedVariable(this.name, this.types, SymbolTable.INSTANCE.getCurrentScope());
        f1.addTypingConstraints(this.types);
        // save the record.
        SymbolTable.INSTANCE.addLocal(f1);

        this.arguments.add(f1);

        this.types.clear();

        return this;
    }

    /**
     * f0 -> <REPEAT>
     * f1 -> IntegerLiteral()
     * f2 -> <TIMES>
     * f3 -> <LBRACE>
     * f4 -> ( Statements() )+
     * f5 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(RepeatStatement n) {
        // super.visit(n);
        // Start a new scope.
        String scopeName = String.format("%s_%d", REPEAT, this.getNextScopeId());
        SymbolTable.INSTANCE.newScope(scopeName);

        n.f1.accept(this);
        Variable f1 = new NamedVariable<Integer>(this.name, SymbolTable.INSTANCE.getCurrentScope());
        f1.setValue(this.integerLiteral);
        f1.addTypingConstraint(NAT);
        addVariable(f1);
        SymbolTable.INSTANCE.addLocal(f1);

        // Get the statements.
        n.f4.accept(this);
        // Return back to old scoping.
        SymbolTable.INSTANCE.endScope();

        return this;
    }

    /**
     * f0 -> <WHILE>
     * f1 -> <LPAREN>
     * f2 -> Conditional()
     * f3 -> <RPAREN>
     * f4 -> <LBRACE>
     * f5 -> ( Statements() )+
     * f6 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(WhileStatement n) {
        // Get the statements.
        n.f4.accept(this);

        return this;
    }

    /**
     * f0 -> <LESSTHAN>
     * | <LESSTHANEQUAL>
     * | <NOTEQUAL>
     * | <EQUALITY>
     * | <GREATERTHAN>
     * | <GREATERTHANEQUAL>
     */
    @Override
    public BSVisitor visit(Conditional n) {
        return super.visit(n);
    }

    /**
     * f0 -> <IF>
     * f1 -> <LPAREN>
     * f2 -> Identifier()
     * f3 -> Conditional()
     * f4 -> Primitives()
     * f5 -> <RPAREN>
     * f6 -> <LBRACE>
     * f7 -> ( Statements() )+
     * f8 -> <RBRACE>
     * f9 -> ( ElseIfBranchStatement() )*
     * f10 -> ( ElseBranchStatement() )?
     */
    @Override
    public BSVisitor visit(BranchStatement n) {
        // Build the instruction.
        // Build the name.
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        // Create a new scope.
        SymbolTable.INSTANCE.newScope(scopeName);
        // Build the variable that resolves a branch evaluation.
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());
        Variable term = new NamedVariable(this.name, SymbolTable.INSTANCE.getCurrentScope());
        term.addTypingConstraint(NAT);
        addVariable(term);
        // End type checking.

        SymbolTable.INSTANCE.addLocal(term);
        // Get the expression.
        n.f2.accept(this);
        // Get the statement.
        n.f7.accept(this);
        // Return back to old scoping.
        SymbolTable.INSTANCE.endScope();

        if (n.f9.present()) {
            n.f9.accept(this);
        }

        if (n.f10.present()) {
            n.f10.accept(this);
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
    public BSVisitor visit(ElseIfBranchStatement n) {
        // super.visit(n);
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        SymbolTable.INSTANCE.newScope(scopeName);

        // Begin type checking.
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());
        Variable term = new NamedVariable(this.name, SymbolTable.INSTANCE.getCurrentScope());
        term.addTypingConstraint(NAT);
        addVariable(term);
        // End type checking.

        SymbolTable.INSTANCE.addLocal(term);
        n.f2.accept(this);
        n.f5.accept(this);
        // Return back to old scoping.
        SymbolTable.INSTANCE.endScope();

        return this;
    }

    /**
     * f0 -> <ELSE>
     * f1 -> <LBRACE>
     * f2 -> Statement()
     * f3 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(ElseBranchStatement n) {
        // super.visit(n);
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        SymbolTable.INSTANCE.newScope(scopeName);
        n.f2.accept(this);
        // Return back to old scoping.
        SymbolTable.INSTANCE.endScope();

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
        }
        return this;
    }

    /**
     * f0 -> <DISPENSE>
     * f1 -> ( VolumeUnit() <OF> )?
     * f2 -> Identifier()
     */
    @Override
    public BSVisitor visit(DispenseStatement n) {
        n.f2.accept(this);
        checkForOrCreateVariable();
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
        String assigned = this.assignTo.getName();
        //super.visit(n);
        n.f1.accept(this);
        checkForOrCreateVariable();

        Set<ChemTypes> types = new HashSet<ChemTypes>(SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope()).getTypes());

        n.f3.accept(this);
        for (int x = 0; x <= this.integerLiteral; x++) {
            this.name = assigned + x;
            checkForOrCreateVariable(types);
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
    public BSVisitor visit(DetectStatement n) {
        // super.visit(n);
        // Get the name
        n.f1.accept(this);
        this.checkForOrCreateVariable();

        n.f3.accept(this);
        this.checkForOrCreateVariable();

        if (n.f4.present()) {
            n.f4.accept(this);
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
     * f3 -> TempUnit()
     * f4 -> ( <FOR> TimeUnit() )?
     */
    @Override
    public BSVisitor visit(HeatStatement n) {
        n.f1.accept(this);
        this.checkForOrCreateVariable();

        n.f3.accept(this);

        //this.checkForOrCreateProperty(f3);

        if (n.f4.present()) {
            n.f4.accept(this);
            // this.checkForOrCreateProperty(f4);
        }
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <ADD>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(PlusExpression n) {
        n.f0.accept(this);
        checkForOrCreateVariable(this.types);
        n.f2.accept(this);
        checkForOrCreateVariable(this.types);
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <MINUS>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(MinusExpression n) {
        n.f0.accept(this);
        checkForOrCreateVariable(this.types);
        n.f2.accept(this);
        checkForOrCreateVariable(this.types);
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <MULTIPLY>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(TimesExpression n) {
        Set<ChemTypes> type = new HashSet<>();

        n.f0.accept(this);
        checkForOrCreateVariable(this.types);
        n.f2.accept(this);
        checkForOrCreateVariable(this.types);
        return this;
    }

    private Variable checkForOrCreateVariable() {
        return checkForOrCreateVariable(new HashSet<>());
    }

    /*
    private Property checkForOrCreateProperty(String units) {
        Property prop;
        Variable var = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, SymbolTable.INSTANCE.getCurrentScope());
        if (var == null) {
            prop = (Property) this.constant;
            // Set<ChemTypes> types = new HashSet<>();
            // types.add(REAL);
            // prop = new Property(this.name, types, SymbolTable.INSTANCE.getCurrentScope());
            prop.setValue(Integer.parseInt(this.value));
            prop.setUnits(units);
            addVariable(prop);
            SymbolTable.INSTANCE.addLocal(prop);
        } else {
            prop = var.converToProperty();
            prop.setUnits(units);
            SymbolTable.INSTANCE.addLocal(prop);
        }
        this.types.clear();
        return prop;
    }*/

    private Variable checkForOrCreateVariable(Set<ChemTypes> inputTypes) {
        Variable declaration = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, SymbolTable.INSTANCE.getCurrentScope());
        if (declaration == null) {
            declaration = new NamedVariable(this.name, SymbolTable.INSTANCE.getCurrentScope());
            if (inputTypes.isEmpty()) {
                declaration.addTypingConstraints(this.getTypingConstraints(declaration));
            } else {
                declaration.addTypingConstraints(inputTypes);
            }
            addVariable(declaration);
            SymbolTable.INSTANCE.addLocal(declaration);
        }
        this.types.clear();
        return declaration;
    }


    public SymbolTable getSymbolTable() {
        return SymbolTable.INSTANCE;
    }

    public String toString() {
        return SymbolTable.INSTANCE.toString();
        //return BSVisitor.statements.toString();
    }


}
