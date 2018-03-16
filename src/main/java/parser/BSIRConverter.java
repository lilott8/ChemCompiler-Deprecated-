package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ir.AssignStatement;
import ir.Conditional;
import ir.DetectStatement;
import ir.DrainStatement;
import ir.HeatStatement;
import ir.IfStatement;
import ir.InvokeStatement;
import ir.LoopStatement;
import ir.ManifestStatement;
import ir.MixStatement;
import ir.ModuleStatement;
import ir.Nop;
import ir.ReturnStatement;
import ir.SinkStatement;
import ir.SourceStatement;
import ir.SplitStatement;
import ir.Statement;
import ir.StatementBlock;
import ir.StationaryStatement;
import parser.ast.AssignmentInstruction;
import parser.ast.BranchStatement;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
import parser.ast.Function;
import parser.ast.FunctionInvoke;
import parser.ast.Manifest;
import parser.ast.Module;
import parser.ast.RepeatStatement;
import parser.ast.Stationary;
import shared.errors.InvalidSyntaxException;
import shared.io.strings.Experiment;
import shared.variable.Property;
import shared.variable.Variable;
import symboltable.SymbolTable;

/**
 * @created: 2/14/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSIRConverter extends BSVisitor {

    public static final Logger logger = LogManager.getLogger(BSIRConverter.class);

    // Are we in assignment?
    private boolean isAssign = false;
    // Manage the left hand side of the expression.
    private Variable assignTo = null;
    // List of functions defined in this program, including the default.
    private Map<String, List<Statement>> functions = new HashMap<>();
    // A simple stack that allows us to know when control changes
    private Deque<Conditional> controlStack = new ArrayDeque<>();
    // Accounting for the methods in this program.
    private Deque<String> methodStack = new ArrayDeque<>();

    private Deque<StatementBlock> listBlocks = new ArrayDeque<>();

    public BSIRConverter(SymbolTable symbolTable) {
        super(symbolTable);
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
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

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
        Variable f2 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

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
        Variable f2 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        ManifestStatement manifest = new ManifestStatement();
        manifest.addInputVariable(f2);
        instructions.put(manifest.getId(), manifest);
        // this.functions.get(SymbolTable.DEFAULT_SCOPE).add(manifest);

        return this;
    }


    /**
     * f0 -> ( TypingList() )?
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     */
    @Override
    public BSVisitor visit(AssignmentInstruction n) {

        // Get the name.
        n.f1.accept(this);
        this.assignTo = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        this.isAssign = true;

        // Get the expression.
        n.f3.accept(this);

        this.isAssign = false;
        // Just to be sure.
        this.assignTo = null;
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
        // Get the name.
        n.f0.accept(this);

        this.method.addStatements(this.functions.get(this.name));

        Statement invoke = new InvokeStatement(this.method);

        // Expand the function into the current tree.
        /*
         * Case: a = func()
         * Point the last instruction to the first method instruction
         * Regenerate ids for the method vertices
         * Build the edges
         * Add the last instruction to the right op
         * Set the last statement
         */
        if (this.isAssign) {
            invoke.addOutputVariable(this.assignTo);
            AssignStatement assign = new AssignStatement();
            assign.setLeftOp(this.assignTo);
            assign.setRightOp(invoke);
            this.addStatement(assign);
        }
        else {
            this.addStatement(invoke);
        }
        instructions.put(invoke.getId(), invoke);
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
        this.method = this.symbolTable.getMethods().get(this.name);

        this.functions.put(this.name, new ArrayList<>());

        // Because we have too.
        n.f3.accept(this);
        logger.warn("Still need to build the parameters to the functions.");

        // Get the statements
        n.f7.accept(this);

        if (n.f8.present()) {
            n.f8.accept(this);
            Statement ret = new ReturnStatement();
            ret.addOutputVariable(this.symbolTable.searchScopesForVariable(this.name));
            ret.addInputVariable(this.symbolTable.searchScopesForVariable(this.name));
            this.method.setReturnStatement(ret);
        }

        StatementBlock block = this.listBlocks.pop();
        for (Map.Entry<Integer, Statement> entry : block.getStatementMap().entrySet()) {
            this.method.addStatement(entry.getValue());
        }

        this.functions.get(this.method.getName()).addAll(this.method.getStatements());
        this.endScope();
        this.methodStack.pop();
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
        Nop source = new SourceStatement();
        Nop sink = new SinkStatement();

        String scopeName = String.format("%s_%d", REPEAT, this.getNextScopeId());
        this.newScope(scopeName);

        n.f1.accept(this);
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the new IR data structure.
        LoopStatement loop = new LoopStatement(f1.toString());
        loop.setScopeName(scopeName);

        // Make sure we set the false target to the sink.
        loop.setFalseTarget(sink);
        loop.setTrueTarget(source);

        this.controlStack.push(loop);
        this.listBlocks.push(new StatementBlock(this.getCurrentScope()));

        // Get the statements.
        n.f4.accept(this);

        this.endScope();
        this.addBranches(loop, true);
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
        // Build the scope for the If Statement.
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        // Create a new scope.
        this.newScope(scopeName);
        // Get the expression.
        logger.warn("Not parsing expression");
        // n.f2.accept(this);
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());

        Variable f2 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        Conditional branch = new IfStatement(f2.toString());
        branch.setScopeName(scopeName);
        instructions.put(branch.getId(), branch);

        // Save the scope/control.
        this.controlStack.push(branch);
        this.listBlocks.push(new StatementBlock(this.getCurrentScope()));

        // Get the statement(s).
        n.f5.accept(this);

        if (n.f7.present() || n.f8.present()) {
            boolean fromElseIf = false;
            // Parse the elseIf(s)
            if (n.f7.present()) {
                fromElseIf = true;
                throw new InvalidSyntaxException("\"else if\" statements are not allowed.");
            }

            // Parse the else
            if (n.f8.present()) {
                scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
                this.newScope(scopeName);
                Conditional elseBranch = new IfStatement("");
                elseBranch.setScopeName(scopeName);
                instructions.put(elseBranch.getId(), elseBranch);

                Nop elseSource = new SourceStatement();
                Nop elseSink = new SinkStatement();

                elseBranch.setFalseTarget(elseSink);
                elseBranch.setTrueTarget(elseSource);

                this.listBlocks.push(new StatementBlock(this.getCurrentScope()));
                this.controlStack.push(elseBranch);

                // Grab the statements.
                n.f8.accept(this);
                // Set the false branch
                if (!fromElseIf) {
                    this.addBranches(elseBranch, false);
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
     * f0 -> <ELSE_IF>
     * f1 -> <LPAREN>
     * f2 -> Expression()
     * f3 -> <RPAREN>
     * f4 -> <LBRACE>
     * f5 -> ( Statement() )+
     * f6 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(ElseIfStatement n) {
        logger.warn("Not parsing expression");
        // n.f2.accept(this);
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());
        // Build a false variable for the expression, for now.
        Variable f2 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        Conditional branch = new IfStatement(f2.toString());
        branch.setScopeName(this.getCurrentScope());

        // Get the statements in the scope.
        n.f5.accept(this);

        return this;
    }

    /**
     * f0 -> <ELSE>
     * f1 -> <LBRACE>
     * f2 -> ( Statement() )+
     * f3 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(ElseStatement n) {
        // Get the statements
        n.f2.accept(this);
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
    public BSVisitor visit(parser.ast.MixStatement n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        n.f3.accept(this);
        Variable f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement mix = new MixStatement();
        mix.addInputVariable(f1);
        mix.addInputVariable(f3);
        mix.addOutputVariable(this.assignTo);

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable<Integer> f4 = this.symbolTable.searchScopeHierarchy(this.name,
                    this.symbolTable.getScopeByName(this.getCurrentScope()));
            // Add f4 to the data structure.
            mix.addProperty(Property.TIME, f4);
        }

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(mix);
        instructions.put(assign.getId(), assign);
        this.addStatement(assign);

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
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        // Get the name.
        n.f3.accept(this);
        Variable<Integer> f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement split = new SplitStatement();
        split.addInputVariable(f1);
        split.addProperty(Property.QUANTITY, f3);
        split.addOutputVariable(this.assignTo);

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(split);
        instructions.put(assign.getId(), assign);
        this.addStatement(assign);


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
    public BSVisitor visit(parser.ast.DetectStatement n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        n.f3.accept(this);
        Variable f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement detect = new DetectStatement();
        detect.addInputVariable(f1);
        detect.addInputVariable(f3);
        detect.addOutputVariable(this.assignTo);

        if (n.f4.present()) {
            n.f4.accept(this);
            logger.warn("this.getNextIntId is being used in detect");
            Variable f4 = this.symbolTable.searchScopeHierarchy(this.name,
                    this.symbolTable.getScopeByName(this.getCurrentScope()));
            // Add f4 to the data structure.
            detect.addProperty(Property.TIME, f4);
        }

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(detect);
        instructions.put(assign.getId(), assign);
        this.addStatement(assign);

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
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement drain = new DrainStatement(String.format("%s-%d",
                DrainStatement.INSTRUCTION, this.getNextInstructionId()));
        drain.addInputVariable(f1);
        // We can add the statement immediately.
        instructions.put(drain.getId(), drain);
        this.addStatement(drain);

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
    public BSVisitor visit(parser.ast.HeatStatement n) {
        // Get the name.
        n.f1.accept(this);
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        // Get the name.
        n.f3.accept(this);
        Variable<Integer> f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement heat = new HeatStatement(String.format("%s-%d",
                HeatStatement.INSTRUCTION, this.getNextInstructionId()));
        heat.addInputVariable(f1);
        heat.addProperty(Property.TEMP, f3);

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable<Integer> f4 = this.symbolTable.searchScopeHierarchy(this.name,
                    this.symbolTable.getScopeByName(this.getCurrentScope()));
            // Add f4 to the data structure.
            heat.addProperty(Property.TIME, f4);
        }

        instructions.put(heat.getId(), heat);
        this.addStatement(heat);

        return this;
    }

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
        if(this.controlStack.size() <= 1) {
            this.functions.get(this.methodStack.peek()).add(conditional);
            controlStack.pop();
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
        if(this.controlStack.isEmpty()) {
            this.functions.get(this.getCurrentScope()).add(statement);
        } else {
            StatementBlock list = this.listBlocks.pop();
            list.addStatement(statement);
            this.listBlocks.push(list);
        }
    }

    public String toString(String indent) {
        StringBuilder sb = new StringBuilder();
        for(Map.Entry<String, List<Statement>> entry : this.functions.entrySet()) {
            sb.append(entry.getKey()).append(": ").append(System.lineSeparator());
            for (Statement s : entry.getValue()) {
                sb.append(s.print(indent)).append(System.lineSeparator());
            }
            sb.append("===========================").append(System.lineSeparator());
        }
        return sb.toString();
    }

    public String toString() {
        Experiment experiment = new Experiment(this.symbolTable, this.functions);
        return experiment.toJson();
    }
}