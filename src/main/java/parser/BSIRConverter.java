package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jgrapht.graph.AbstractBaseGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedPseudograph;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import ir.blocks.BlockGraph;
import ir.graph.Assign;
import ir.graph.AssignStatement;
import ir.graph.Conditional;
import ir.graph.DetectStatement;
import ir.graph.DrainStatement;
import ir.graph.HeatStatement;
import ir.graph.InvokeStatement;
import ir.graph.LoopStatement;
import ir.graph.ManifestStatement;
import ir.graph.MixStatement;
import ir.graph.ModuleStatement;
import ir.graph.Nop;
import ir.graph.SinkStatement;
import ir.graph.SourceStatement;
import ir.graph.SplitStatement;
import ir.graph.Statement;
import ir.graph.StationaryStatement;
import ir.soot.Experiment;
import parser.ast.AssignmentInstruction;
import parser.ast.BranchStatement;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
import parser.ast.FormalParameter;
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

    private Experiment experiment = new Experiment(1, "Experiment");
    private boolean isAssign = false;
    // Manage the left hand side of the expression.
    private Variable assignTo = null;

    private boolean inMethod = false;
    // The graph of the IR.
    private AbstractBaseGraph<Statement, DefaultEdge> statements = new DirectedPseudograph<>(DefaultEdge.class);
    // A simple stack that allows us to know when control changes
    private Deque<Conditional> controlStack = new ArrayDeque<>();
    // The previous statement we were on.
    private Statement previousStatement;
    // Temporary jumps for control flow movement.
    private BlockGraph blocks = new BlockGraph();
    private Map<String, Statement> sinkStatements = new HashMap<>();
    private Map<Integer, Statement> instructions = new LinkedHashMap<>();

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
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        AssignStatement assign = new AssignStatement();
        ModuleStatement module = new ModuleStatement();
        module.addInputVariable(f1);
        assign.setRightOp(module);
        this.resolveBranch(assign);
        this.blocks.addToBlock(assign);
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
        this.resolveBranch(assign);
        this.blocks.addToBlock(assign);
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
        this.resolveBranch(assign);
        this.blocks.addToBlock(assign);
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

        if (isAssign) {
            AssignStatement assign = new AssignStatement();
            assign.setLeftOp(this.assignTo);
            assign.setRightOp(invoke);
        }

        this.resolveBranch(invoke);
        this.blocks.addToBlock(invoke);
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
        // Get a new scope.
        this.newScope(this.name);
        // Build the method.
        this.method = this.symbolTable.getMethods().get(this.name);
        this.inMethod = true;
        // Add the method.
        this.experiment.addMethods(this.method);

        // Because we have too.
        n.f3.accept(this);

        // Get the statements
        n.f7.accept(this);

        if (n.f8.present()) {
            n.f8.accept(this);
        }
        this.inMethod = false;

        this.endScope();
        return this;
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(FormalParameter n) {
        // Go fetch the typing list
        n.f0.accept(this);
        // Go fetch the name
        n.f1.accept(this);
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
        Nop sink = new SinkStatement();
        this.statements.addVertex(sink);

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

        Conditional branch = new ir.graph.IfStatement(f2.toString());
        branch.setScopeName(scopeName);
        this.blocks.addToBlock(branch);
        this.blocks.newBranchBlock();

        this.controlStack.push(branch);

        // Get the statement(s).
        n.f5.accept(this);

        this.endScope();
        this.blocks.endBranchBlock();
        this.controlStack.pop();

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
                n.f8.accept(this);
                Conditional elseBranch = this.controlStack.pop();
                // Set the false branch
                if (!fromElseIf) {
                    branch.setFalseTarget(elseBranch);
                } else {
                    // get the last else if statement
                    // and point the false branch here.
                }
                this.endScope();
            }
        } else {
            branch.setFalseTarget(sink);
            this.statements.addEdge(branch, sink);
            this.previousStatement.setFallsThrough(true);
            this.statements.addEdge(this.previousStatement, sink);
        }

        this.previousStatement = sink;

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

        this.blocks.addToBlock(loop);
        this.blocks.newBranchBlock(source);

        // Get the statements.
        n.f4.accept(this);

        this.endScope();

        this.blocks.newBranchBlock(sink);
        this.blocks.addEdge(loop, sink);
        this.blocks.addEdge(this.previousStatement, loop);

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

        Conditional branch = new ir.graph.IfStatement(f2.toString());
        branch.setScopeName(this.getCurrentScope());
        this.blocks.addToBlock(branch);
        this.blocks.newBranchBlock();

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

        Conditional branch = new ir.graph.IfStatement("");
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
        this.resolveBranch(mix);
        this.blocks.addToBlock(assign);
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
        this.resolveBranch(split);
        this.blocks.addToBlock(assign);
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
        this.resolveBranch(detect);
        this.blocks.addToBlock(assign);
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
        this.resolveBranch(drain);
        this.blocks.addToBlock(drain);
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

        this.resolveBranch(heat);
        this.blocks.addToBlock(heat);
        this.previousStatement = heat;
        this.instructions.put(heat.getId(), heat);

        return this;
    }

    private void addStatement(Statement statement) {

    }

    private void resolveBranch(Statement statement) {
        // If the stack is empty, we don't do anything to it.
        /*if (!this.controlStack.isEmpty()) {
            // If these don't match, then we know we've finished a branching
            // series and need to put the input statement as the next statement.
            logger.info(this.controlStack.peekFirst().getScopeName() +"\t" + this.getCurrentScope());
            if (!StringUtils.equalsIgnoreCase(this.controlStack.peekFirst().getScopeName(), this.getCurrentScope())) {
                logger.fatal("Scopes don't match!");
                // Pop off the current branch to mutate
                Conditional currentBranch = this.controlStack.getFirst();
                currentBranch.setFalseTarget(statement);
                // Add it to the graph
                this.statements.addVertex(statement);
                this.statements.addEdge(currentBranch, statement);
            } else {
                this.statements.addVertex(statement);
                this.statements.addEdge(this.previousStatement, statement);
            }
        } else {*/
        //this.statements.addVertex(statement);
        //if (this.previousStatement != null) {
        //this.statements.addEdge(this.previousStatement, statement);
        //  }
        //}
        this.previousStatement = statement;
    }

    public void writeToDisk() {
        this.blocks.writeToDisk();
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