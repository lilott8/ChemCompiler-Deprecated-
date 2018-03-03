package parser;

import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;

import java.util.ArrayDeque;
import java.util.Deque;

import ir.graph.AssignStatement;
import ir.graph.Block;
import ir.graph.Conditional;
import ir.graph.DetectStatement;
import ir.graph.DrainStatement;
import ir.graph.HeatStatement;
import ir.graph.InvokeStatement;
import ir.graph.LoopStatement;
import ir.graph.MixStatement;
import ir.graph.SplitStatement;
import ir.graph.Statement;
import ir.soot.instruction.Assign;
import ir.soot.instruction.Detect;
import ir.soot.instruction.Drain;
import ir.soot.Experiment;
import ir.soot.instruction.Heat;
import ir.soot.instruction.Instruction;
import ir.soot.instruction.Invoke;
import ir.soot.instruction.Mix;
import ir.soot.instruction.Split;
import ir.soot.statement.Branch;
import ir.soot.statement.Loop;
import parser.ast.Assignment;
import parser.ast.DetectInstruction;
import parser.ast.DrainInstruction;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
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
import typesystem.elements.Formula;

/**
 * @created: 2/14/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSIRConverter extends BSVisitor {

    private Experiment experiment = new Experiment(1, "Experiment");
    private boolean isAssign = false;


    //List<Statement> statements = new ArrayList<>();
    private Statement statement;
    private boolean inMethod = false;
    private boolean inLoop = false;
    private boolean inBranch = false;
    private boolean convergeControl = false;
    private Graph<Statement, DefaultEdge> statements = new DefaultDirectedGraph<>(DefaultEdge.class);
    private Deque<Statement> branchStack = new ArrayDeque<>();
    private Deque<Block> blocks = new ArrayDeque<>();
    private Statement previousStatement;
    private Statement skipBranch;



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
        addVariable(f1);

        this.instruction = new Assign();
        this.instruction.addInputVariable(f1);
        this.instruction.addOutputVariable(f1);
        addInstruction(this.instruction);

        // Build the IR data structure.
        this.experiment.addModule(f1);
        this.experiment.addInstruction(this.instruction);

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
        addVariable(f2);

        // Build the IR data structure.
        this.instruction = new ir.soot.instruction.Manifest();
        this.instruction.addInputVariable(f2);
        this.instruction.addTypes(f2.getTypes());

        addInstruction(this.instruction);

        this.experiment.addStationary(f2);
        this.experiment.addInstruction(this.instruction);

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
        addVariable(f2);

        // Build the IR data structure.
        this.instruction = new ir.soot.instruction.Manifest();
        this.instruction.addInputVariable(f2);
        this.instruction.addTypes(f2.getTypes());

        addInstruction(this.instruction);

        // Build the IR data structure.
        this.experiment.addManifest(f2);
        this.experiment.addInstruction(this.instruction);

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

        n.f7.accept(this);

        this.inMethod = false;

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

        // this.instruction = new Branch();
        // this.instruction.addInputVariable(f2);

        logger.fatal("If branch has no branching... yet");

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
        Variable f2 = variables.get(this.scopifyName());

        // this.instruction = new Branch();
        // this.instruction.addInputVariable(f2);

        logger.fatal("ElseIf branch has no branching... yet");

        // Get the statements in the scope.
        n.f5.accept(this);
        // TODO: figure out a way to add the branch to a

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


        // Get the statements
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
        this.isAssign = true;

        // Get the name.
        n.f1.accept(this);
        Variable f1 = variables.get(this.scopifyName());

        this.statement = new AssignStatement();
        this.statement.addInputVariable(f1);
        this.isAssign = true;

        Assign instr = new Assign();
        instr.addOutputVariable(f1);

        // Get the expression.
        n.f3.accept(this);


        /*
        if (this.assignToFunction) {
            instr.addInputVariable(this.method);
            this.assignToFunction = false;
        } else {
            instr.addInstruction(this.instruction);
        }*/

        this.experiment.addInstruction(instr);

        this.isAssign = false;
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

        Statement mix = new MixStatement();
        mix.addInputVariable(f1);
        mix.addInputVariable(f3);

        // Build the IR data structure.
        Instruction instruction = new Mix();
        instruction.addInputVariable(f1);
        instruction.addInputVariable(f3);
        instruction.addTypes(f1.getTypes());
        instruction.addTypes(f3.getTypes());

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = variables.get(this.scopifyName());
            // Add f4 to the data structure.
            instruction.addProperty(f4);
            mix.addProperty(f4);
        }

        logger.fatal("mix shouldn't add the instruction until the assignment");
        this.experiment.addInstruction(instruction);

        logger.info("Mix is converted");
        ((AssignStatement)this.statement).setRightOp(mix);
        this.addInstruction(this.statement);

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

        Statement split = new SplitStatement();
        split.addInputVariable(f1);
        split.addProperty(f3);
        ((AssignStatement)this.statement).setRightOp(split);
        this.addInstruction(this.statement);

        logger.info("Split is converted");

        // Build the IR data structure.
        Instruction instruction = new Split();
        instruction.addInputVariable(f1);
        instruction.addProperty(f3);
        instruction.addTypes(f1.getTypes());

        logger.fatal("split shouldn't add the instruction until the assignment");
        this.experiment.addInstruction(instruction);

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

        Statement drain = new DrainStatement();
        drain.addInputVariable(f1);
        this.addInstruction(drain);

        logger.info("Drain is converted");

        // Build the IR data structure.
        Instruction instr = new Drain();
        instr.addInputVariable(f1);
        instr.addTypes(f1.getTypes());
        this.experiment.addInstruction(instr);

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

        Statement heat = new HeatStatement();
        heat.addInputVariable(f1);
        heat.addInputVariable(f3);

        // Build the IR data structure.
        Instruction instr = new Heat();
        instr.addInputVariable(f1);
        instr.addProperty(f3);

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = variables.get(this.scopifyName());
            // Add f4 to the data structure.
            instr.addProperty(f4);
            heat.addProperty(f4);
        }

        logger.info("Heat is converted");

        this.experiment.addInstruction(instr);
        this.addInstruction(heat);

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

        Statement detect = new DetectStatement();
        detect.addInputVariable(f1);
        detect.addInputVariable(f3);

        // Build the IR data structure.
        this.instruction = new Detect();
        this.instruction.addInputVariable(f1);
        this.instruction.addInputVariable(f3);

        if (n.f4.present()) {
            n.f4.accept(this);
            Variable f4 = variables.get(this.scopifyName());
            // Add f4 to the data structure.
            this.instruction.addProperty(f4);
            detect.addProperty(f4);
        }


        logger.fatal("detect shouldn't add the instruction until the assignment");
        this.experiment.addInstruction(this.instruction);

        logger.info("Detect is converted");
        ((AssignStatement) this.statement).setRightOp(detect);
        this.addInstruction(this.statement);

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
        Variable f1 = variables.get(this.scopifyName());

        // Build the new IR data structure.
        LoopStatement loop = new LoopStatement(f1.toString());
        this.addInstruction(loop);
        this.branchStack.push(loop);
        this.inLoop = true;

        // Get the statements.
        n.f4.accept(this);

        this.inLoop = false;
        this.convergeControl = true;

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
        // Get the name.
        n.f0.accept(this);

        this.method = this.symbolTable.getMethods().get(this.name);

        Statement invoke = new InvokeStatement(this.method);

        if (isAssign) {
            ((AssignStatement)this.statement).setRightOp(invoke);
            this.addInstruction(this.statement);
        } else {
            this.addInstruction(invoke);
        }

        logger.info("Invoke is converted");

        return this;
    }

    public String toString() {
        return this.experiment.toString();
    }



    private void addInstruction(Statement statement) {
        // If in a branch, then add it to the queue of the block.
        if (!this.branchStack.isEmpty()) {
            Block block = this.blocks.pop();
            block.addStatement(statement);
            this.blocks.push(block);
        }
        // This case handles the back propagation.
        else if (this.convergeControl) {
            Block block = this.blocks.pop();
            Conditional conditional = (Conditional) this.branchStack.pop();

            this.convergeControl = false;
        }
        // Handle the methods.
        else if (this.inMethod) {
            this.statements.addVertex(statement);
            this.method.addStatement(statement);
        }
        // Just add it to the graph.
        else {
            this.statements.addVertex(statement);
            this.statements.addEdge(this.previousStatement, statement);
            this.previousStatement = statement;
        }
    }
}