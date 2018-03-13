package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import ir.graph.BlockGraph;
import ir.statements.Conditional;
import ir.statements.Statement;
import parser.ast.BranchStatement;
import parser.ast.DetectStatement;
import parser.ast.DrainStatement;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
import parser.ast.ExpressionList;
import parser.ast.ExpressionRest;
import parser.ast.FormalParameter;
import parser.ast.FormalParameterList;
import parser.ast.FormalParameterRest;
import parser.ast.Function;
import parser.ast.FunctionInvoke;
import parser.ast.HeatStatement;
import parser.ast.InstructionAssignment;
import parser.ast.Manifest;
import parser.ast.MixStatement;
import parser.ast.Module;
import parser.ast.RepeatStatement;
import parser.ast.SplitStatement;
import parser.ast.Stationary;
import parser.ast.Type;
import parser.ast.TypingList;
import parser.ast.TypingRest;
import shared.Step;
import symboltable.SymbolTable;

/**
 * @created: 3/12/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSJsonConverter extends BSVisitor {

    public static final Logger logger = LogManager.getLogger(BSJsonConverter.class);

    // A simple stack that allows us to know when control changes
    private Deque<Conditional> controlStack = new ArrayDeque<>();
    private Deque<String> methodStack = new ArrayDeque<>();
    // The previous statement we were on.
    private Statement previousStatement;
    // Maps the function we are in with the appropriate graph.
    private Map<String, BlockGraph> graphs = new HashMap<>();
    private Map<Integer, Statement> instructions = new LinkedHashMap<>();
    private int id = 0;

    private StringBuilder json = new StringBuilder("{").append(Statement.NL);

    public BSJsonConverter(SymbolTable symbolTable) {
        super(symbolTable);
        this.graphs.put(SymbolTable.DEFAULT_SCOPE, new BlockGraph());
        this.methodStack.push(SymbolTable.DEFAULT_SCOPE);
    }

    @Override
    public Step run() {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }

    private int getNextId() {
        return id++;
    }

    /**
     * f0 -> <MODULE>
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(Module n) {
        n.f1.accept(this);
        json.append("\"SENSOR_DECLARATION\" : {").append(Statement.NL);
        json.append("\"ID\" : ").append(this.getNextId()).append(",").append(Statement.NL);
        json.append("\"NAME\" : \"").append(this.name).append("\",").append(Statement.NL);
        json.append("\"TYPE\" : \"SENSOR\"").append(Statement.NL).append("}").append(Statement.NL);
        json.append(",").append(Statement.NL);
        return this;
    }

    /**
     * f0 -> <STATIONARY>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Stationary n) {
        n.f1.accept(this);
        n.f2.accept(this);
        logger.warn("Figure out what to do with types.");

        json.append("\"VARIABLE_DECLARATION\" : {").append(Statement.NL);
        json.append("\"ID\" : ").append(this.getNextId()).append(",").append(Statement.NL);
        json.append("\"NAME\" : \"").append(this.name).append("\",").append(Statement.NL);
        json.append("\"TYPE\" : \"").append("STATIONARY").append("\"").append(Statement.NL);
        json.append("}").append(Statement.NL);

        return this;
    }

    /**
     * f0 -> <MANIFEST>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Manifest n) {
        n.f1.accept(this);
        n.f2.accept(this);
        logger.warn("Figure out what to do with types.");

        return super.visit(n);
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
        return super.visit(n);
    }

    /**
     * f0 -> Type()
     * f1 -> ( TypingRest() )*
     */
    @Override
    public BSVisitor visit(TypingList n) {
        return super.visit(n);
    }

    /**
     * f0 -> MatLiteral()
     * | NatLiteral()
     * | RealLiteral()
     */
    @Override
    public BSVisitor visit(Type n) {
        return super.visit(n);
    }

    /**
     * f0 -> <COMMA>
     * f1 -> Type()
     */
    @Override
    public BSVisitor visit(TypingRest n) {
        return super.visit(n);
    }

    /**
     * f0 -> FormalParameter()
     * f1 -> ( FormalParameterRest() )*
     */
    @Override
    public BSVisitor visit(FormalParameterList n) {
        return super.visit(n);
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(FormalParameter n) {
        return super.visit(n);
    }

    /**
     * f0 -> <COMMA>
     * f1 -> FormalParameter()
     */
    @Override
    public BSVisitor visit(FormalParameterRest n) {
        return super.visit(n);
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
        return super.visit(n);
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> IntegerLiteral()
     */
    @Override
    public BSVisitor visit(SplitStatement n) {
        return super.visit(n);
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(DrainStatement n) {
        return super.visit(n);
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
        return super.visit(n);
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
        return super.visit(n);
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
        return super.visit(n);
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
        return super.visit(n);
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
        return super.visit(n);
    }

    /**
     * f0 -> <ELSE>
     * f1 -> <LBRACE>
     * f2 -> ( Statement() )+
     * f3 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(ElseStatement n) {
        return super.visit(n);
    }

    /**
     * f0 -> Identifier()
     * f1 -> <LPAREN>
     * f2 -> ( ExpressionList() )?
     * f3 -> <RPAREN>
     */
    @Override
    public BSVisitor visit(FunctionInvoke n) {
        return super.visit(n);
    }

    /**
     * f0 -> Expression()
     * f1 -> ( ExpressionRest() )*
     */
    @Override
    public BSVisitor visit(ExpressionList n) {
        return super.visit(n);
    }

    /**
     * f0 -> <COMMA>
     * f1 -> Expression()
     */
    @Override
    public BSVisitor visit(ExpressionRest n) {
        return super.visit(n);
    }

    /**
     * f0 -> MixStatement()
     * | DetectStatement()
     * | SplitStatement()
     * | FunctionInvoke()
     */
    @Override
    public BSVisitor visit(InstructionAssignment n) {
        return super.visit(n);
    }

    public String toString() {
        logger.info("Adding closing curly bracket in toString");
        return this.json.append("}").toString();
    }
}
