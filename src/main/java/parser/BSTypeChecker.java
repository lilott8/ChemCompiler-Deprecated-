package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import parser.ast.AssignmentInstruction;
import parser.ast.BSProgram;
import parser.ast.BranchStatement;
import parser.ast.DetectStatement;
import parser.ast.DrainStatement;
import parser.ast.Function;
import parser.ast.HeatStatement;
import parser.ast.Manifest;
import parser.ast.MixStatement;
import parser.ast.Module;
import parser.ast.Node;
import parser.ast.RepeatStatement;
import parser.ast.SplitStatement;
import parser.ast.Stationary;
import parser.visitor.GJNoArguDepthFirst;
import shared.Step;
import symboltable.SymbolTable;
import typesystem.epa.ChemTypes;

/**
 * @created: 11/30/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSTypeChecker extends GJNoArguDepthFirst<Node> implements Step, TypeChecker {

    public static final Logger logger = LogManager.getLogger(BSTypeChecker.class);

    private SymbolTable symbolTable;
    private String name;
    private Set<ChemTypes> types;
    private Set<ChemTypes> inferredTypes;
    private Map<String, Set<ChemTypes>> typingConstraints = new HashMap<>();

    public BSTypeChecker(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    @Override
    public String getName() {
        return "BSTypeChecker";
    }

    @Override
    public Step run() {
        return this;
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     */
    @Override
    public Node visit(AssignmentInstruction n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <MODULE>
     * f1 -> Identifier()
     */
    @Override
    public Node visit(Module n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <STATIONARY>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public Node visit(Stationary n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <MANIFEST>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public Node visit(Manifest n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <FUNCTION>
     * f1 -> Identifier()
     * f2 -> <LPAREN>
     * f3 -> ( FormalParameterList() )*
     * f4 -> <RPAREN>
     * f5 -> ( <COLON> TypingList() )?
     * f6 -> <LBRACE>
     * f7 -> ( Statement() )*
     * f8 -> ( <RETURN> Expression() )?
     * f9 -> <RBRACE>
     */
    @Override
    public Node visit(Function n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <MIX>
     * f1 -> PrimaryExpression()
     * f2 -> <WITH>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Node visit(MixStatement n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> IntegerLiteral()
     */
    @Override
    public Node visit(SplitStatement n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    @Override
    public Node visit(DrainStatement n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <HEAT>
     * f1 -> PrimaryExpression()
     * f2 -> <AT>
     * f3 -> IntegerLiteral()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Node visit(HeatStatement n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <DETECT>
     * f1 -> PrimaryExpression()
     * f2 -> <ON>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public Node visit(DetectStatement n) {
        // super.visit(n);

        return null;
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
    public Node visit(RepeatStatement n) {
        // super.visit(n);

        return null;
    }

    /**
     * f0 -> <IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE_IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE> <LBRACE> Statement() <RBRACE>
     */
    @Override
    public Node visit(BranchStatement n) {
        // super.visit(n);

        return null;
    }
}
