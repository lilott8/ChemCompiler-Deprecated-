package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jgrapht.Graph;
import org.jgrapht.Graphs;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import ir.graph.BlockGraph;
import ir.graph.Edge;
import ir.statements.Assign;
import ir.statements.AssignStatement;
import ir.statements.Conditional;
import ir.statements.DetectStatement;
import ir.statements.DrainStatement;
import ir.statements.HeatStatement;
import ir.statements.InvokeStatement;
import ir.statements.LoopStatement;
import ir.statements.ManifestStatement;
import ir.statements.MixStatement;
import ir.statements.ModuleStatement;
import ir.statements.Nop;
import ir.statements.SinkStatement;
import ir.statements.SourceStatement;
import ir.statements.SplitStatement;
import ir.statements.Statement;
import ir.statements.StationaryStatement;
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
    private boolean graphsCombined = false;

    private boolean inMethod = false;
    // A simple stack that allows us to know when control changes
    private Deque<Conditional> controlStack = new ArrayDeque<>();
    private Deque<String> methodStack = new ArrayDeque<>();
    // The previous statement we were on.
    private Statement previousStatement;
    // Maps the function we are in with the appropriate graph.
    private Map<String, BlockGraph> graphs = new HashMap<>();
    private Map<Integer, Statement> instructions = new LinkedHashMap<>();


    public BSIRConverter(SymbolTable symbolTable) {
        super(symbolTable);
        this.graphs.put(SymbolTable.DEFAULT_SCOPE, new BlockGraph());
        this.methodStack.push(SymbolTable.DEFAULT_SCOPE);
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
        AssignStatement assign = new AssignStatement();
        ModuleStatement module = new ModuleStatement();
        module.addInputVariable(f1);
        assign.setRightOp(module);
        this.graphs.get(this.methodStack.peek()).addToBlock(assign);
        this.instructions.put(assign.getId(), assign);

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
        AssignStatement assign = new AssignStatement();
        StationaryStatement stationary = new StationaryStatement();
        stationary.addInputVariable(f2);
        assign.setRightOp(stationary);
        this.graphs.get(this.methodStack.peek()).addToBlock(assign);
        this.instructions.put(assign.getId(), assign);

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
        AssignStatement assign = new AssignStatement();
        ManifestStatement manifest = new ManifestStatement();
        manifest.addInputVariable(f2);
        assign.setRightOp(manifest);
        this.graphs.get(this.methodStack.peek()).addToBlock(assign);
        this.instructions.put(assign.getId(), assign);

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

        this.method = this.symbolTable.getMethods().get(this.name);

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
        //Statement entry = this.method.getBlockGraph().firstStatement();
        //Statement exit = this.method.getBlockGraph().finalStatement();
        //this.graphs.get(this.methodStack.peek()).addToBlock(entry);
        //Graph<Statement, Edge> methodGraph = this.method.getBlockGraph().getGraph();

        if (this.isAssign) {
            AssignStatement assign = new AssignStatement();
            assign.setLeftOp(this.assignTo);
            //assign.setRightOp(exit);
            assign.setRightOp(invoke);
        }
        // case:
        // func()
        else {
            //this.graphs.get(this.methodStack.peek()).addToBlock(exit);
            this.graphs.get(this.methodStack.peek()).addToBlock(invoke);
        }

        this.previousStatement = invoke;
        this.instructions.put(invoke.getId(), invoke);

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
        // Get a new scope.
        this.newScope(this.name);
        this.methodStack.push(this.name);
        this.graphs.put(this.name, new BlockGraph());
        // Build the method.
        this.method = this.symbolTable.getMethods().get(this.name);
        this.inMethod = true;

        // Because we have too.
        n.f3.accept(this);

        // Get the statements
        n.f7.accept(this);

        if (n.f8.present()) {
            n.f8.accept(this);
        }
        this.inMethod = false;

        this.endScope();
        this.method.addStatements(this.graphs.get(this.methodStack.peek()));
        this.methodStack.pop();
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
        Nop branchFalse = new SinkStatement();
        Nop branchSource = new SourceStatement();

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

        Conditional branch = new ir.statements.IfStatement(f2.toString());
        branch.setScopeName(scopeName);
        this.instructions.put(branch.getId(), branch);

        // Set the targets to the appropriate
        // Source/Sink targets, for simplification.
        branch.setFalseTarget(branchFalse);
        branch.setTrueTarget(branchSource);
        // Add the branch to the block.
        this.graphs.get(this.methodStack.peek()).addToBlock(branch);
        // Create a new basic block.
        this.graphs.get(this.methodStack.peek()).newBranchBlock(branchSource);
        // Save the scope/control.
        this.controlStack.push(branch);

        // Get the statement(s).
        n.f5.accept(this);

        this.endScope();
        // End the block for this.
        this.controlStack.pop();

        // Add the new sink.
        this.graphs.get(this.methodStack.peek()).addToBlock(branchFalse);
        // Create the edge between the branch and sink.
        this.graphs.get(this.methodStack.peek()).addEdge(branch, branchFalse);

        if (n.f7.present() || n.f8.present()) {
            boolean fromElseIf = false;
            // Parse the elseIf(s)
            if (n.f7.present()) {
                fromElseIf = true;
                // scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
                // this.newScope(scopeName);
                // n.f1.accept(this);
                // this.previousStatement.setFallsThrough(true);
                // this.statements.addEdge(this.previousStatement, sink);
                // this.endScope();
                throw new InvalidSyntaxException("\"else if\" statements are not allowed.");
            }

            // Parse the else
            if (n.f8.present()) {
                scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
                this.newScope(scopeName);
                Conditional elseBranch = new ir.statements.IfStatement("");
                elseBranch.setScopeName(scopeName);
                this.instructions.put(elseBranch.getId(), elseBranch);

                Nop elseSource = new SourceStatement();
                Nop elseSink = new SinkStatement();

                elseBranch.setFalseTarget(elseSink);
                elseBranch.setTrueTarget(elseSource);

                // Create a block that doesn't fall through.
                this.graphs.get(this.methodStack.peek()).newElseBlock(elseBranch);
                // Add the source for this block.
                this.graphs.get(this.methodStack.peek()).addToBlock(elseSource);
                this.controlStack.push(elseBranch);

                // Grab the statements.
                n.f8.accept(this);
                // Set the false branch
                if (!fromElseIf) {
                    // Add the sink
                    this.graphs.get(this.methodStack.peek()).addToBlock(elseSink);
                    // Remove the connection between the branch,
                    // And it's sink.  It is redundant.
                    this.graphs.get(this.methodStack.peek()).removeEdge(branch, branchFalse);
                    // Connect the branch to the else.
                    this.graphs.get(this.methodStack.peek()).addEdge(branch, elseBranch);
                    // Connect the branch sink with the else.
                    this.graphs.get(this.methodStack.peek()).addEdge(branchFalse, elseSink);
                } else {
                    // This is only necessary if the else if is in use.
                    // Add the last else if to this else.
                    // this.graph.addEdge();
                    // get the last else if statement
                    // and point the false branch here.
                }
                this.controlStack.pop();
                this.endScope();
            }
        }

        this.previousStatement = branchFalse;

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

        this.graphs.get(this.methodStack.peek()).addToBlock(loop);
        this.graphs.get(this.methodStack.peek()).newBranchBlock(source);

        // Get the statements.
        n.f4.accept(this);

        this.endScope();

        // We need this block, because we don't
        // Want the previous instruction to fall through.
        this.graphs.get(this.methodStack.peek()).newElseBlock(sink);
        // This edge is the loop exiting.
        this.graphs.get(this.methodStack.peek()).addEdge(loop, sink);
        // This edge is the loop back into the condition.
        this.graphs.get(this.methodStack.peek()).addEdge(this.previousStatement, loop);

        this.instructions.put(loop.getId(), loop);

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

        Conditional branch = new ir.statements.IfStatement(f2.toString());
        branch.setScopeName(this.getCurrentScope());
        this.graphs.get(this.methodStack.peek()).addToBlock(branch);
        this.graphs.get(this.methodStack.peek()).newBranchBlock();

        this.controlStack.push(branch);
        // Get the statements in the scope.
        n.f5.accept(this);
        this.previousStatement.setFallsThrough(true);

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

        Conditional branch = new ir.statements.IfStatement("");
        branch.setScopeName(this.getCurrentScope());
        this.controlStack.push(branch);
        // Get the statements
        n.f2.accept(this);

        // Save the last node in the control block,
        // So we know where to fall through from.
        this.previousStatement.setFallsThrough(true);

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

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = this.symbolTable.searchScopeHierarchy(this.name,
                    this.symbolTable.getScopeByName(this.getCurrentScope()));
            // Add f4 to the data structure.
            mix.addProperty(f4);
        }

        // this.experiment.addInstruction(instruction);
        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(mix);
        this.graphs.get(this.methodStack.peek()).addToBlock(assign);
        this.previousStatement = assign;
        this.instructions.put(assign.getId(), assign);

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
        Variable f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement split = new SplitStatement();
        split.addInputVariable(f1);
        split.addProperty(f3);

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(split);
        this.graphs.get(this.methodStack.peek()).addToBlock(assign);
        this.previousStatement = assign;
        this.instructions.put(assign.getId(), assign);

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

        if (n.f4.present()) {
            n.f4.accept(this);
            logger.warn("this.getNextIntId is being used in detect");
            Variable f4 = this.symbolTable.searchScopeHierarchy(this.name,
                    this.symbolTable.getScopeByName(this.getCurrentScope()));
            // Add f4 to the data structure.
            detect.addProperty(f4);
        }

        AssignStatement assign = new AssignStatement();
        assign.setLeftOp(this.assignTo);
        assign.setRightOp(detect);
        this.graphs.get(this.methodStack.peek()).addToBlock(assign);
        this.previousStatement = assign;
        this.instructions.put(assign.getId(), assign);

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
        this.graphs.get(this.methodStack.peek()).addToBlock(drain);
        this.previousStatement = drain;
        this.instructions.put(drain.getId(), drain);

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
        Variable f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement heat = new HeatStatement(String.format("%s-%d",
                HeatStatement.INSTRUCTION, this.getNextInstructionId()));
        heat.addInputVariable(f1);
        heat.addInputVariable(f3);

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = this.symbolTable.searchScopeHierarchy(this.name,
                    this.symbolTable.getScopeByName(this.getCurrentScope()));
            // Add f4 to the data structure.
            heat.addProperty(f4);
        }

        this.graphs.get(this.methodStack.peek()).addToBlock(heat);
        this.previousStatement = heat;
        this.instructions.put(heat.getId(), heat);

        return this;
    }

    private void combineGraphs() {
        Graph<Statement, Edge> mainGraph = this.graphs.get(SymbolTable.DEFAULT_SCOPE).getGraph();
        // We don't want to iterate this graph.
        this.graphs.remove(SymbolTable.DEFAULT_SCOPE);
        // These are the remaining methods that need to be integrated into the graph.
        for (Map.Entry<String, BlockGraph> entry : this.graphs.entrySet()) {
            logger.warn("Combining: " + entry.getKey());
            Graphs.addGraph(mainGraph, entry.getValue().getGraph());
        }
        this.graphsCombined = true;
        writeToDisk(mainGraph);
    }

    public void writeToDisk() {
        if (!this.graphsCombined) {
            this.combineGraphs();
        }
        BlockGraph.writeToDisk(this.graphs);
    }

    private void writeToDisk(Graph<Statement, Edge> graph) {
        BlockGraph.writeToDisk(graph);
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<Integer, Statement> entry : this.instructions.entrySet()) {
            if (entry.getValue() instanceof Assign) {
                Assign temp = (Assign) entry.getValue();
                sb.append(temp.getId()).append(System.lineSeparator());
            } else if (entry.getValue() instanceof Conditional) {
                Conditional temp = (Conditional) entry.getValue();
                sb.append(temp.getId()).append(temp.getName()).append(" TRUE:").append(System.lineSeparator());
                sb.append(temp.getTrueTarget()).append(System.lineSeparator());
                sb.append(temp.getId()).append(temp.getName()).append(" FALSE:").append(System.lineSeparator());
                sb.append(temp.getFalseTarget()).append(System.lineSeparator());
            } else {
                sb.append(entry.getValue().getName());
            }
        }
        return sb.toString();
    }
}