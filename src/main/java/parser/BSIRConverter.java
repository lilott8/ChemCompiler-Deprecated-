package parser;

import java.util.ArrayDeque;
import java.util.Deque;

import parser.ast.Assignment;
import parser.ast.BSProgram;
import parser.ast.DetectInstruction;
import parser.ast.DrainInstruction;
import parser.ast.ElseIfStatement;
import parser.ast.ElseStatement;
import parser.ast.FalseLiteral;
import parser.ast.FunctionDefinition;
import parser.ast.FunctionInvoke;
import parser.ast.HeatInstruction;
import parser.ast.Identifier;
import parser.ast.IfStatement;
import parser.ast.IntegerLiteral;
import parser.ast.Manifest;
import parser.ast.MatLiteral;
import parser.ast.MixInstruction;
import parser.ast.Module;
import parser.ast.NatLiteral;
import parser.ast.RealLiteral;
import parser.ast.RepeatInstruction;
import parser.ast.SplitInstruction;
import parser.ast.Stationary;
import parser.ast.TrueLiteral;
import parser.visitor.GJNoArguDepthFirst;

/**
 * @created: 2/14/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSIRConverter extends BSVisitor {

    private Deque<String> scope = new ArrayDeque<>();

    @Override
    public BSVisitor run() {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }

    /**
     * f0 -> ( Module() )*
     * f1 -> ( Stationary() )*
     * f2 -> ( Manifest() )+
     * f3 -> <INSTRUCTIONS>
     * f4 -> ( Sequence() )+
     * f5 -> <EOF>
     */
    @Override
    public BSVisitor visit(BSProgram n) {
        return super.visit(n);
    }

    /**
     * f0 -> <MODULE>
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(Module n) {
        return super.visit(n);
    }

    /**
     * f0 -> <STATIONARY>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Stationary n) {
        return super.visit(n);
    }

    /**
     * f0 -> <MANIFEST>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Manifest n) {
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
    public BSVisitor visit(FunctionDefinition n) {
        return super.visit(n);
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
    public BSVisitor visit(ElseIfStatement n) {
        return super.visit(n);
    }

    /**
     * f0 -> <ELSE>
     * f1 -> <LBRACE>
     * f2 -> Statement()
     * f3 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(ElseStatement n) {
        return super.visit(n);
    }

    /**
     * f0 -> ( TypingList() )?
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     */
    @Override
    public BSVisitor visit(Assignment n) {
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
    public BSVisitor visit(MixInstruction n) {
        return super.visit(n);
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> IntegerLiteral()
     */
    @Override
    public BSVisitor visit(SplitInstruction n) {
        return super.visit(n);
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(DrainInstruction n) {
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
    public BSVisitor visit(HeatInstruction n) {
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
    public BSVisitor visit(DetectInstruction n) {
        return super.visit(n);
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
     * f0 -> <INTEGER_LITERAL>
     */
    @Override
    public BSVisitor visit(IntegerLiteral n) {
        return super.visit(n);
    }

    /**
     * f0 -> <NAT>
     */
    @Override
    public BSVisitor visit(NatLiteral n) {
        return super.visit(n);
    }

    /**
     * f0 -> <MAT>
     */
    @Override
    public BSVisitor visit(MatLiteral n) {
        return super.visit(n);
    }

    /**
     * f0 -> <REAL>
     */
    @Override
    public BSVisitor visit(RealLiteral n) {
        return super.visit(n);
    }

    /**
     * f0 -> <TRUE>
     */
    @Override
    public BSVisitor visit(TrueLiteral n) {
        return super.visit(n);
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public BSVisitor visit(FalseLiteral n) {
        return super.visit(n);
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    @Override
    public BSVisitor visit(Identifier n) {
        return super.visit(n);
    }

}