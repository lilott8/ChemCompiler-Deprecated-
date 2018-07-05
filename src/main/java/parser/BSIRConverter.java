package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import chemical.epa.ChemTypes;
import ir.AssignStatement;
import ir.Conditional;
import ir.DetectStatement;
import ir.DrainStatement;
import ir.HeatStatement;
import ir.IfStatement;
import ir.InvokeStatement;
import ir.LoopStatement;
import ir.ManifestStatement;
import ir.MathStatement;
import ir.MixStatement;
import ir.ModuleStatement;
import ir.ReturnStatement;
import ir.SplitStatement;
import ir.Statement;
import ir.StatementBlock;
import ir.StationaryStatement;
import parser.ast.AllowedArguments;
import parser.ast.AllowedArgumentsRest;
import parser.ast.ArgumentList;
import parser.ast.AssignmentStatement;
import parser.ast.BranchStatement;
import parser.ast.DispenseStatement;
import parser.ast.ElseBranchStatement;
import parser.ast.ElseIfBranchStatement;
import parser.ast.FormalParameter;
import parser.ast.FormalParameterList;
import parser.ast.FormalParameterRest;
import parser.ast.FunctionDefinition;
import parser.ast.FunctionInvoke;
import parser.ast.IntegerLiteral;
import parser.ast.Manifest;
import parser.ast.MinusExpression;
import parser.ast.Module;
import parser.ast.PlusExpression;
import parser.ast.RepeatStatement;
import parser.ast.Stationary;
import parser.ast.TimesExpression;
import parser.ast.VariableAlias;
import parser.ast.WhileStatement;
import shared.errors.InvalidSyntaxException;
import shared.io.strings.Experiment;
import shared.properties.Property;
import shared.properties.Quantity;
import shared.properties.Temperature;
import shared.properties.Time;
import shared.properties.Volume;
import shared.variable.Variable;
import symboltable.SymbolTable;

/**
 * @created: 2/14/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSIRConverter extends BSVisitor {

    public static final Logger logger = LogManager.getLogger(BSIRConverter.class);

    // List of functions defined in this program, including the default.
    private Map<String, List<Statement>> functions = new HashMap<>();
    // A simple stack that allows us to know when control changes
    private Deque<Conditional> controlStack = new ArrayDeque<>();
    // Accounting for the methods in this program.
    private Deque<String> methodStack = new ArrayDeque<>();

    private Deque<StatementBlock> listBlocks = new ArrayDeque<>();

    public BSIRConverter() {
        super();
        this.methodStack.push(SymbolTable.DEFAULT_SCOPE);
        this.listBlocks.push(new StatementBlock(this.getCurrentScope()));
        this.functions.put(SymbolTable.DEFAULT_SCOPE, new ArrayList<>());
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
        Variable f1 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        // Build the IR data structure.
        ModuleStatement module = new ModuleStatement();
        module.addInputVariable(f1);
        instructions.put(module.getId(), module);
        // this.functions.get(SymbolTable.DEFAULT_SCOPE).add(module);

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
        Variable f2 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        // Build the IR data structure.
        StationaryStatement stationary = new StationaryStatement();
        stationary.addInputVariable(f2);
        // this.graphs.get(this.methodStack.peek()).addToBlock(stationary);
        instructions.put(stationary.getId(), stationary);
        // this.functions.get(SymbolTable.DEFAULT_SCOPE).add(stationary);

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
        Variable f2 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        // Build the IR data structure.
        ManifestStatement manifest = new ManifestStatement();
        manifest.addInputVariable(f2);
        instructions.put(manifest.getId(), manifest);
        // this.functions.get(SymbolTable.DEFAULT_SCOPE).add(manifest);

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
        // Get the name.
        n.f1.accept(this);
        this.assignTo = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        this.isAssign = true;

        // Get the RightOp.
        n.f3.accept(this);

        this.isAssign = false;
        // Just to be sure.
        this.assignTo = null;
        return this;
    }

    /**
     * f0 -> Identifier()
     * f1 -> <LPAREN>
     * f2 -> ( ArgumentList() )?
     * f3 -> <RPAREN>
     */
    @Override
    public BSVisitor visit(FunctionInvoke n) {
        // Get the name.
        n.f0.accept(this);

        this.method.addStatements(this.functions.get(this.name));

        Statement invoke = new InvokeStatement(this.method);

        // We don't want to include the name of the function,
        // Just the parameters, thus we mark true here.
        this.inInvoke = true;

        if (n.f2.present()) {
            n.f2.accept(this);
            invoke.addInputVariables(this.parameters);
            this.parameters.clear();
        }

        // Expand the function into the current tree.
        /*
         * Case: a = func()
         * Point the last instruction to the first method instruction
         * Regenerate ids for the method vertices
         * Build the edges
         * Add the last instruction to the right op
         * Set the last statement
         */
        invoke.setMethodName(this.methodStack.peek());
        if (this.isAssign) {
            invoke.addOutputVariable(this.assignTo);
            AssignStatement assign = new AssignStatement();
            assign.setLeftOp(this.assignTo);
            assign.setRightOp(invoke);
            this.addStatement(assign);
        } else {
            this.addStatement(invoke);
        }
        instructions.put(invoke.getId(), invoke);
        this.inInvoke = false;
        this.types.clear();
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
        this.methodStack.push(this.name);
        this.functions.put(this.name, new ArrayList<>());
        // Get a new scope.
        this.newScope(this.name);
        this.listBlocks.push(new StatementBlock(this.getCurrentScope()));
        this.methodStack.push(this.name);
        // Build the method.
        this.method = SymbolTable.INSTANCE.getMethods().get(this.name);

        this.functions.put(this.name, new ArrayList<>());

        if (n.f3.present()) {
            n.f3.accept(this);
            //this.method.addParameters(this.parameters);
            this.parameters.clear();
        }

        // Get the statements
        n.f7.accept(this);

        if (n.f8.present()) {
            n.f8.accept(this);
            Statement ret = new ReturnStatement();
            ret.addOutputVariable(SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope()));
            ret.addInputVariable(SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope()));
            this.method.setReturnStatement(ret);
        } else {
            logger.fatal("Add exception for no return statement.");
        }

        StatementBlock block = this.listBlocks.pop();
        for (Map.Entry<Integer, Statement> entry : block.getStatementMap().entrySet()) {
            this.method.addStatement(entry.getValue());
        }

        this.functions.get(this.method.getName()).addAll(this.method.getStatements());
        SymbolTable.INSTANCE.addMethod(this.method);
        this.endScope();
        this.methodStack.pop();
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
        n.f1.accept(this);
        Variable v = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());
        if (n.f0.present()) {
            n.f0.accept(this);
            if (v != null && v.getTypes().isEmpty()) {
                v.addTypingConstraints(this.types);
                this.types.clear();
            }
        }
        this.parameters.add(v);
        return this;
    }

    /**
     * f0 -> AllowedArguments()
     * f1 -> ( AllowedArgumentsRest() )*
     */
    @Override
    public BSVisitor visit(ArgumentList n) {
        n.f0.accept(this);

        if (n.f1.present()) {
            n.f1.accept(this);
        }
        return this;
    }

    /**
     * f0 -> <COMMA>
     * f1 -> AllowedArguments()
     */
    @Override
    public BSVisitor visit(AllowedArgumentsRest n) {
        n.f1.accept(this);
        return this;
    }

    /**
     * f0 -> Identifier()
     * | Primitives()
     */
    @Override
    public BSVisitor visit(AllowedArguments n) {
        n.f0.accept(this);

        Variable v = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());
        this.parameters.add(v);
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
        String scopeName = String.format("%s_%d", REPEAT, this.getNextScopeId());
        this.newScope(scopeName);

        n.f1.accept(this);
        this.name = String.format("%s_%s", CONST, n.f0.toString());
        // Build the new IR data structure.
        LoopStatement loop = new LoopStatement(this.name);
        loop.setCondition(n.f1.f0.toString());
        loop.setScopeName(scopeName);
        loop.setMethodName(this.methodStack.peek());
        this.types.clear();

        this.controlStack.push(loop);
        this.listBlocks.push(new StatementBlock(this.getCurrentScope()));

        // Get the statements.
        n.f4.accept(this);

        this.endScope();
        this.addBranches(loop, true);
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
        String scopeName = String.format("%s_%d", REPEAT, this.getNextScopeId());
        this.newScope(scopeName);
        n.f1.accept(this);

        n.f2.accept(this);
        //Variable f1 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
        //        this.getCurrentScope());

        // Build the new IR data structure.
        LoopStatement loop = new LoopStatement(this.conditional);
        loop.setScopeName(scopeName);
        loop.setMethodName(this.methodStack.peek());
        this.types.clear();

        this.controlStack.push(loop);
        this.listBlocks.push(new StatementBlock(this.getCurrentScope()));

        // Get the statements.
        n.f4.accept(this);

        this.endScope();
        this.addBranches(loop, true);
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
     *
     *
     *
     * ((IntegerLiteral)n.f1.choice).f0.toString()
     */
    @Override
    public BSVisitor visit(BranchStatement n) {
        // Build the scope for the If Statement.
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        // Create a new scope.
        this.newScope(scopeName);
        // Get the expression.
        this.inConditional = true;
        n.f2.accept(this);
        String conditional = this.name;
        n.f3.accept(this);
        conditional += n.f3.f0.choice.toString();
        n.f4.accept(this);
        conditional += this.integerLiteral;
        this.inConditional = false;

        Conditional elseBranch = null;

        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());


        Variable f2 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        Conditional branch = new IfStatement(conditional, true);
        branch.setScopeName(scopeName);
        branch.setMethodName(this.methodStack.peek());
        instructions.put(branch.getId(), branch);

        // Save the scope/control.
        this.controlStack.push(branch);
        this.listBlocks.push(new StatementBlock(this.getCurrentScope()));

        // Get the statement(s).
        n.f7.accept(this);

        if (n.f9.present() || n.f10.present()) {
            boolean fromElseIf = false;
            // Parse the elseIf(s)
            if (n.f9.present()) {
                fromElseIf = true;
                throw new InvalidSyntaxException("\"else if\" statements are not allowed.");
            }

            // Parse the else
            if (n.f10.present()) {
                scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
                this.newScope(scopeName);
                elseBranch = new IfStatement("", false);
                elseBranch.setScopeName(scopeName);
                elseBranch.setMethodName(this.methodStack.peek());
                instructions.put(elseBranch.getId(), elseBranch);

                this.listBlocks.push(new StatementBlock(this.getCurrentScope()));
                // this.controlStack.push(elseBranch);

                // Grab the statements.
                n.f9.accept(this);

                // Set the false branch
                if (!fromElseIf) {
                    this.addBranches(branch, false);
                } else {
                    // This is only necessary if the else if is in use.
                    // Add the last else if to this else.
                    // this.graph.addEdge();
                    // get the last else if statement
                    // and point the false branch here.
                }
                this.endScope();
            }
        }
        // End the block for this.
        // ControlStack pops in here.
        this.addBranches(branch, true);
        this.endScope();

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
    public BSVisitor visit(parser.ast.Conditional n) {
        return super.visit(n);
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
        this.inConditional = true;
        n.f2.accept(this);
        this.inConditional = false;
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());
        // Build a false variable for the expression, for now.
        Variable f2 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        Conditional branch = new IfStatement(this.conditional, false);
        branch.setScopeName(this.getCurrentScope());
        branch.setMethodName(this.methodStack.peek());

        // Get the statements in the scope.
        n.f5.accept(this);
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
        // Get the statements
        n.f2.accept(this);
        return this;
    }

    /**
     * f0 -> <MIX>
     * f1 -> ( VolumeUnit() <OF> )?
     * f2 -> PrimaryExpression()
     * f3 -> <WITH>
     * f4 -> ( VolumeUnit() <OF> )?
     * f5 -> PrimaryExpression()
     * f6 -> ( <FOR> TimeUnit() )?
     */
    @Override
    public BSVisitor visit(parser.ast.MixStatement n) {
        Property f1;
        if (n.f1.present()) {
            n.f1.accept(this);
            f1 = new Volume(this.name, this.units, this.integerLiteral);
        } else {
            f1 = new Volume("unknown", "UL", 10);
        }

        // Get the name.
        n.f2.accept(this);
        Variable f2 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());
        f2.setProperty(f1);

        Property f4;
        if (n.f4.present()) {
            n.f4.accept(this);
            f4 = new Volume(this.name, this.units, this.integerLiteral);
        } else {
            f4 = new Volume("unknown", "UL", 10);
        }
        n.f5.accept(this);
        Variable f5 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());
        f5.setProperty(f4);

        // Build the IR data structure.
        Statement mix = new MixStatement();
        mix.addInputVariable(f2);
        mix.addInputVariable(f5);
        mix.addOutputVariable(this.assignTo);

        Property f6;
        if (n.f6.present()) {
            n.f6.accept(this);
            f6 = new Time(this.name, this.units, this.integerLiteral);
        } else {
            f6 = new Time("unknown", "SECOND", 1);
        }
        mix.addProperty(Property.TIME, f6);

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(mix);
        mix.setMethodName(this.methodStack.peek());

        instructions.put(assign.getId(), assign);
        // this.addStatement(assign);
        this.addStatement(mix);

        return this;
    }

    /**
     * f0 -> <DISPENSE>
     * f1 -> ( VolumeUnit() <OF> )?
     * f2 -> Identifier()
     */
    @Override
    public BSVisitor visit(DispenseStatement n) {
        Property f1;
        if (n.f1.present()) {
            n.f1.accept(this);
            f1 = new Volume(this.name, this.units, this.integerLiteral);
        } else {
            f1 = new Volume("unknown", "UL", 10);
        }
        n.f2.accept(this);
        Variable f2 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());
        f2.setProperty(f1);

        Statement dispense = new ir.DispenseStatement();
        dispense.addInputVariable(f2);
        dispense.addProperty(Property.VOLUME, f1);
        dispense.addOutputVariable(this.assignTo);

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(dispense);
        dispense.setMethodName(this.methodStack.peek());

        this.addStatement(dispense);

        return this;
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> IntegerLiteral()
     */
    @Override
    public BSVisitor visit(parser.ast.SplitStatement n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());
        // Get the name.
        n.f3.accept(this);
        Property f3 = new Quantity("SPLIT", "SPLIT", this.integerLiteral);

        // Build the IR data structure.
        Statement split = new SplitStatement();
        split.addInputVariable(f1);
        split.addProperty(Property.QUANTITY, f3);
        String name;
        for (int x = 1; x <= this.integerLiteral; x++) {
            name = this.assignTo.getName() + x;
            Variable var = SymbolTable.INSTANCE.searchScopeHierarchy(name, this.getCurrentScope());
            split.addOutputVariable(var);
        }
        // split.addOutputVariable(this.assignTo);

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(split);
        split.setMethodName(this.methodStack.peek());
        instructions.put(assign.getId(), assign);
        // this.addStatement(assign);
        this.addStatement(split);

        return this;
    }

    /**
     * f0 -> <DETECT>
     * f1 -> PrimaryExpression()
     * f2 -> <ON>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> TimeUnit() )?
     */
    @Override
    public BSVisitor visit(parser.ast.DetectStatement n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());
        n.f3.accept(this);
        Variable f3 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        // Build the IR data structure.
        Statement detect = new DetectStatement();
        detect.addInputVariable(f1);
        detect.addInputVariable(f3);
        detect.addOutputVariable(this.assignTo);

        Property f4;
        if (n.f4.present()) {
            n.f4.accept(this);
            f4 = new Time(this.name, this.units, this.integerLiteral);
            // Add f4 to the data structure.
        } else {
            f4 = new Time("unknown", "SECONDS", 10);
        }
        detect.addProperty(Property.TIME, f4);

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(detect);
        detect.setMethodName(this.methodStack.peek());
        instructions.put(assign.getId(), assign);
        // this.addStatement(assign);
        this.addStatement(detect);

        return this;
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(parser.ast.DrainStatement n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        // Build the IR data structure.
        Statement drain = new DrainStatement(String.format("%s-%d",
                DrainStatement.INSTRUCTION, this.getNextInstructionId()));
        drain.addInputVariable(f1);
        drain.setMethodName(this.methodStack.peek());
        // We can add the statement immediately.
        instructions.put(drain.getId(), drain);
        this.addStatement(drain);

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
    public BSVisitor visit(parser.ast.HeatStatement n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = SymbolTable.INSTANCE.searchScopeHierarchy(this.name,
                this.getCurrentScope());

        // Get the name.
        n.f3.accept(this);
        Property f3 = new Temperature(this.name, this.units, this.integerLiteral);

        // Build the IR data structure.
        Statement heat = new HeatStatement(String.format("%s-%d",
                HeatStatement.INSTRUCTION, this.getNextInstructionId()));

        heat.addInputVariable(f1);
        heat.addProperty(Property.TEMP, f3);

        if (n.f4.present()) {
            n.f4.accept(this);
            Property f4 = new Time(this.name, this.units, (float) this.integerLiteral);
            // Add f4 to the data structure.
            heat.addProperty(Property.TIME, f4);
        }
        heat.setMethodName(this.methodStack.peek());

        instructions.put(heat.getId(), heat);
        this.addStatement(heat);

        return this;
    }

    /**
     * f0 -> Identifier()
     */
    @Override
    public BSVisitor visit(VariableAlias n) {
        n.f0.accept(this);

        Variable rightOp = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());

        Set<ChemTypes> rightOpTypes = new HashSet<ChemTypes>(rightOp.getTypes());

        rightOpTypes.removeAll(ChemTypes.getNums());

        if (!ChemTypes.getMaterials().isEmpty()) {
            // Compiler.abandonShip("You cannot assign a material to a variable.");
            throw new InvalidSyntaxException("You cannot alias a material (e.g. mat x = y.");
        } else {
            AssignStatement assign = new AssignStatement();
            MathStatement math = new MathStatement();
            math.addInputVariable(rightOp);
            math.addOutputVariable(rightOp);
            math.setMethodName(this.methodStack.peek());
            assign.setLeftOp(this.assignTo);
            assign.setRightOp(math);
            assign.setMethodName(this.methodStack.peek());
            instructions.put(assign.getId(), assign);
            this.addStatement(assign);
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
        Variable a = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());
        n.f2.accept(this);
        Variable b = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());

        Statement math = new MathStatement();
        math.addInputVariable(a);
        math.addInputVariable(b);
        math.addOutputVariable(this.assignTo);
        math.setMethodName(this.methodStack.peek());
        this.addStatement(math);

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
        Variable a = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());
        n.f2.accept(this);
        Variable b = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());

        Statement math = new MathStatement();
        math.addInputVariable(a);
        math.addInputVariable(b);
        math.addOutputVariable(this.assignTo);
        math.setMethodName(this.methodStack.peek());
        this.addStatement(math);
        return this;
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <MULTIPLY>
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(TimesExpression n) {
        n.f0.accept(this);
        Variable a = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());
        n.f2.accept(this);
        Variable b = SymbolTable.INSTANCE.searchScopeHierarchy(this.name, this.getCurrentScope());

        Statement math = new MathStatement();
        math.addInputVariable(a);
        math.addInputVariable(b);
        math.addOutputVariable(this.assignTo);
        math.setMethodName(this.methodStack.peek());
        this.addStatement(math);
        return this;
    }


    /**
     * Determines how to add a branch to the list of instructions.
     * If there is no nested control, it simply adds it to the list.
     * Otherwise, it must be added to the stack and continue on.
     */
    private Conditional addBranches(Conditional conditional, boolean branch) {
        StatementBlock block = this.listBlocks.pop();
        for (Map.Entry<Integer, Statement> entry : block.getStatementMap().entrySet()) {
            if (branch) {
                conditional.addToTrueBranch(entry.getValue());
            } else {
                conditional.addToFalseBranch(entry.getValue());
            }
        }
        // This is a control in the main.
        if (this.controlStack.size() <= 1) {
            this.functions.get(this.methodStack.peek()).add(conditional);
            if (!this.controlStack.isEmpty()) {
                controlStack.pop();
            }
        } else {
            // This is a nested control.
            Conditional inner = this.controlStack.pop();
            Conditional outer = this.controlStack.pop();
            block = this.listBlocks.pop();
            if (branch) {
                for (Map.Entry<Integer, Statement> entry : block.getStatementMap().entrySet()) {
                    outer.addToTrueBranch(entry.getValue());
                }
                outer.addToTrueBranch(conditional);
            } else {
                for (Map.Entry<Integer, Statement> entry : block.getStatementMap().entrySet()) {
                    outer.addToFalseBranch(entry.getValue());
                }
                outer.addToFalseBranch(conditional);
            }
            this.controlStack.push(outer);
            block.clear();
            this.listBlocks.push(block);
        }
        return null;
    }

    public void addStatement(Statement statement) {
        if (this.controlStack.isEmpty()) {
            this.functions.get(this.getCurrentScope()).add(statement);
        } else {
            StatementBlock list = this.listBlocks.pop();
            list.addStatement(statement);
            this.listBlocks.push(list);
        }
    }

    public String toString(String indent) {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<String, List<Statement>> entry : this.functions.entrySet()) {
            sb.append(entry.getKey()).append(": ").append(System.lineSeparator());
            for (Statement s : entry.getValue()) {
                sb.append(s.print(indent)).append(System.lineSeparator());
            }
            sb.append("===========================").append(System.lineSeparator());
        }
        return sb.toString();
    }

    public String toString() {
        Experiment experiment = new Experiment(SymbolTable.INSTANCE, this.functions);
        return experiment.toJson();
    }
}