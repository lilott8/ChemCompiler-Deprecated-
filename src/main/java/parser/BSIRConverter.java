package parser;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jgrapht.Graph;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayDeque;
import java.util.Deque;

import chemical.epa.ChemTypes;
import config.ConfigFactory;
import ir.graph.AssignStatement;
import ir.graph.Block;
import ir.graph.Conditional;
import ir.graph.DetectStatement;
import ir.graph.DrainStatement;
import ir.graph.HeatStatement;
import ir.graph.InvokeStatement;
import ir.graph.LoopStatement;
import ir.graph.ManifestStatement;
import ir.graph.MixStatement;
import ir.graph.ModuleStatement;
import ir.graph.SplitStatement;
import ir.graph.Statement;
import ir.graph.StationaryStatement;
import ir.soot.Experiment;
import parser.ast.Assignment;
import parser.ast.DetectInstruction;
import parser.ast.DrainInstruction;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
import parser.ast.FormalParameter;
import parser.ast.FunctionDefinition;
import parser.ast.FunctionInvoke;
import parser.ast.HeatInstruction;
import parser.ast.IfStatement;
import parser.ast.Manifest;
import parser.ast.MixInstruction;
import parser.ast.Module;
import parser.ast.RepeatInstruction;
import parser.ast.SplitInstruction;
import parser.ast.Stationary;
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

    //List<Statement> statements = new ArrayList<>();
    private Statement statement;
    private boolean inMethod = false;
    // The graph of the IR.
    private Graph<Statement, DefaultEdge> statements = new DefaultDirectedGraph<>(DefaultEdge.class);
    // A simple stack that allows us to know when control changes
    private Deque<Statement> controlStack = new ArrayDeque<>();
    // The corresponding stack for the blocks associated with a control change.
    private Deque<Block> blocks = new ArrayDeque<>();
    // The previous statement we were on.
    private Statement previousStatement;


    public BSIRConverter(SymbolTable symbolTable) {
        super(symbolTable);
        this.blocks.push(new Block());
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
        AssignStatement assign = new AssignStatement(String.format("%s-%d",
                AssignStatement.INSTRUCTION, this.getNextInstructionId()));
        ModuleStatement module = new ModuleStatement(String.format("%s-%d",
                ModuleStatement.INSTRUCTION, this.getNextInstructionId()));
        module.addInputVariable(f1);
        assign.setRightOp(module);
        this.resolveBranch(assign);

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
        AssignStatement assign = new AssignStatement(String.format("%s-%d",
                AssignStatement.INSTRUCTION, this.getNextInstructionId()));
        StationaryStatement stationary = new StationaryStatement(String.format("%s-%d",
                StationaryStatement.INSTRUCTION, this.getNextInstructionId()));
        stationary.addInputVariable(f2);
        assign.setRightOp(stationary);
        this.resolveBranch(assign);

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
        AssignStatement assign = new AssignStatement(String.format("%s-%d",
                AssignStatement.INSTRUCTION, this.getNextInstructionId()));
        ManifestStatement manifest = new ManifestStatement(String.format("%s-%d",
                ManifestStatement.INSTRUCTION, this.getNextInstructionId()));
        manifest.addInputVariable(f2);
        assign.setRightOp(manifest);
        this.resolveBranch(assign);

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

        // Get the name.
        n.f1.accept(this);
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        this.statement = new AssignStatement(String.format("%s-%d", AssignStatement.INSTRUCTION,
                this.getNextInstructionId()));
        this.statement.addInputVariable(f1);
        this.isAssign = true;

        // Get the expression.
        n.f3.accept(this);

        this.resolveBranch(this.statement);

        /*
        if (this.assignToFunction) {
            instr.addInputVariable(this.method);
            this.assignToFunction = false;
        } else {
            instr.addInstruction(this.instruction);
        }*/

        this.isAssign = false;
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

        Statement invoke = new InvokeStatement(this.method.getName(), this.method);

        if (isAssign) {
            ((AssignStatement)this.statement).setRightOp(invoke);
        } else {
            this.resolveBranch(invoke);
        }

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
        logger.info("in formal parameter");
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
        String scopeName = String.format("%s_%d", REPEAT, this.getNextScopeId());
        this.newScope(scopeName);

        n.f1.accept(this);
        logger.warn("name: " + scopeName + "_" + this.name);
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        logger.info(f1);

        // Build the new IR data structure.
        LoopStatement loop = new LoopStatement(String.format("%s-%d", LoopStatement.INSTRUCTION,
                this.getNextInstructionId()), f1.toString());
        this.statements.addVertex(loop);
        this.statements.addEdge(this.previousStatement, loop);
        // Save the instruction on the control stack.
        this.controlStack.push(loop);

        // Get the statements.
        n.f4.accept(this);

        this.endScope();

        // Keep the previous statement so we can add
        // the branches to it.
        this.previousStatement = this.controlStack.pop();

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
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        // Create a new scope.
        this.newScope(scopeName);
        // Get the expression.
        logger.warn("Not parsing expression");
        // n.f2.accept(this);
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());

        Variable f2 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        Conditional statement = new ir.graph.IfStatement(String.format("%s-%d",
                ir.graph.IfStatement.INSTRUCTION, this.getNextInstructionId()), f2.toString());
        this.statements.addVertex(statement);
        this.statements.addEdge(this.previousStatement, statement);
        this.controlStack.push(statement);

        // Get the statement.
        n.f5.accept(this);

        // Return back to old scoping.
        this.endScope();
        // Save the instruction as the last instruction.
        this.previousStatement = this.controlStack.pop();

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
        String scopeName = String.format("%s_%d", BRANCH, this.getNextScopeId());
        this.newScope(scopeName);

        // Get the expression.
        logger.warn("Not parsing expression");
        // n.f2.accept(this);
        this.name = String.format("%s_%d", INTEGER, this.getNextIntId());
        logger.warn(String.format("%s_%s", this.getCurrentScope(), this.name));
        Variable f2 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        logger.warn(f2);

        Conditional elseIf = new ir.graph.IfStatement(String.format("%s-%d",
                ir.graph.IfStatement.INSTRUCTION, this.getNextInstructionId()), f2.toString());
        ((Conditional) this.previousStatement).setFalseTarget(elseIf);
        this.statements.addVertex(elseIf);
        this.statements.addEdge(this.previousStatement, elseIf);
        this.controlStack.push(elseIf);

        // Get the statements in the scope.
        n.f5.accept(this);

        // Return back to old scoping.
        this.endScope();
        this.previousStatement = this.controlStack.pop();
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
        this.newScope(scopeName);

        Conditional elseStatement = new ir.graph.IfStatement(String.format("%s-%d",
                ir.graph.IfStatement.INSTRUCTION, this.getNextInstructionId()), "");
        ((Conditional) this.previousStatement).setFalseTarget(elseStatement);
        this.statements.addVertex(elseStatement);
        this.statements.addEdge(this.previousStatement, elseStatement);
        this.controlStack.push(elseStatement);

        // Get the statements
        n.f2.accept(this);
        // Return back to old scoping.
        this.endScope();
        this.previousStatement = this.controlStack.pop();
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
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        n.f3.accept(this);
        Variable f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement mix = new MixStatement(String.format("%s-%d",
                MixStatement.INSTRUCTION, this.getNextInstructionId()));
        mix.addInputVariable(f1);
        mix.addInputVariable(f3);


        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = this.symbolTable.searchScopeHierarchy(this.name,
                    this.symbolTable.getScopeByName(this.getCurrentScope()));
            // Add f4 to the data structure.
            mix.addProperty(f4);
        }

        this.experiment.addInstruction(instruction);

        ((AssignStatement)this.statement).setRightOp(mix);

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
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        // Get the name.
        n.f3.accept(this);
        Variable f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement split = new SplitStatement(String.format("%s-%d", SplitStatement.INSTRUCTION,
                this.getNextInstructionId()));
        split.addInputVariable(f1);
        split.addProperty(f3);
        ((AssignStatement)this.statement).setRightOp(split);

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
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));
        n.f3.accept(this);
        Variable f3 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement detect = new DetectStatement(String.format("%s-%d", DetectStatement.INSTRUCTION,
                this.getNextInstructionId()));
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

        ((AssignStatement) this.statement).setRightOp(detect);

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
        Variable f1 = this.symbolTable.searchScopeHierarchy(this.name,
                this.symbolTable.getScopeByName(this.getCurrentScope()));

        // Build the IR data structure.
        Statement drain = new DrainStatement(String.format("%s-%d",
                DrainStatement.INSTRUCTION, this.getNextInstructionId()));
        drain.addInputVariable(f1);
        // We can add the statement immediately.
        this.resolveBranch(drain);

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

        return this;
    }

    private void resolveBranch(Statement statement) {
        // If the stack is empty, we don't do anything to it.
        if (!this.controlStack.isEmpty()) {
            // If these don't match, then we know we've finished a branching
            // series and need to put the input statement as the next statement.
            if (!StringUtils.equalsIgnoreCase(this.controlStack.peek().getName(), this.getCurrentScope())) {
                // Pop off the current branch to mutate
                Conditional currentBranch = (Conditional) this.controlStack.peek();
                currentBranch.setFalseTarget(statement);
                // Add it to the graph
                this.statements.addVertex(statement);
                this.statements.addEdge(currentBranch, statement);
            } else {
                // Block block = this.blocks.pop();
                // block.addStatement(statement);
                this.statements.addVertex(statement);
                // this.statements.addEdge(block.getLastStatement(), statement);
                this.statements.addEdge(this.previousStatement, statement);
                this.previousStatement = statement;
                // this.blocks.push(block);
            }
        } else {
            this.statements.addVertex(statement);
            if (this.previousStatement != null) {
                this.statements.addEdge(this.previousStatement, statement);
            }
            this.previousStatement = statement;
        }
    }

    public void writeToDisk() {
        try (FileOutputStream fileOutputStream = new FileOutputStream(ConfigFactory.getConfig().getOutputDir() + "graph.dot");
             OutputStreamWriter writer = new OutputStreamWriter(fileOutputStream, "UTF-8")) {
            DOTExporter<Statement, DefaultEdge> exporter = new DOTExporter<>();
            exporter.export(writer, this.statements);
        } catch(IOException e) {
            logger.fatal(e.getMessage());
            e.printStackTrace();
        }
    }

    public String toString() {
        return this.experiment.toString();
    }
}