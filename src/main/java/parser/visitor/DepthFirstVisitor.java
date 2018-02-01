//
// Generated by JTB 1.3.2
//

package parser.visitor;

import java.util.Enumeration;

import parser.ast.AndExpression;
import parser.ast.AssignmentStatement;
import parser.ast.BSProgram;
import parser.ast.BranchStatement;
import parser.ast.DetectStatement;
import parser.ast.DrainStatement;
import parser.ast.EqualityExpression;
import parser.ast.Expression;
import parser.ast.FalseLiteral;
import parser.ast.FormalParameter;
import parser.ast.FormalParameterList;
import parser.ast.FormalParameterRest;
import parser.ast.Function;
import parser.ast.GreaterThanEqualExpression;
import parser.ast.GreaterThanExpression;
import parser.ast.HeatStatement;
import parser.ast.Identifier;
import parser.ast.Instruction;
import parser.ast.IntegerLiteral;
import parser.ast.LessThanEqualExpression;
import parser.ast.LessThanExpression;
import parser.ast.Manifest;
import parser.ast.MatLiteral;
import parser.ast.MinusExpression;
import parser.ast.MixStatement;
import parser.ast.Module;
import parser.ast.NatLiteral;
import parser.ast.Node;
import parser.ast.NodeList;
import parser.ast.NodeListOptional;
import parser.ast.NodeOptional;
import parser.ast.NodeSequence;
import parser.ast.NodeToken;
import parser.ast.NotEqualExpression;
import parser.ast.NotExpression;
import parser.ast.OrExpression;
import parser.ast.ParenthesisExpression;
import parser.ast.PlusExpression;
import parser.ast.PrimaryExpression;
import parser.ast.RealLiteral;
import parser.ast.RepeatStatement;
import parser.ast.SplitStatement;
import parser.ast.Statement;
import parser.ast.Stationary;
import parser.ast.TimesExpression;
import parser.ast.TrueLiteral;
import parser.ast.Type;
import parser.ast.TypingList;
import parser.ast.TypingRest;
import parser.ast.WhileStatement;

/**
 * Provides default methods which visit each node in the tree in depth-first
 * order.  Your visitors may extend this class.
 */
public class DepthFirstVisitor implements Visitor {
    //
    // Auto class visitors--probably don't need to be overridden.
    //
    public void visit(NodeList n) {
        for (Enumeration<Node> e = n.elements(); e.hasMoreElements(); )
            e.nextElement().accept(this);
    }

    public void visit(NodeListOptional n) {
        if (n.present())
            for (Enumeration<Node> e = n.elements(); e.hasMoreElements(); )
                e.nextElement().accept(this);
    }

    public void visit(NodeOptional n) {
        if (n.present())
            n.node.accept(this);
    }

    public void visit(NodeSequence n) {
        for (Enumeration<Node> e = n.elements(); e.hasMoreElements(); )
            e.nextElement().accept(this);
    }

    public void visit(NodeToken n) {
    }

    //
    // User-generated visitor methods below
    //

    /**
     * f0 -> Module()
     * f1 -> Stationary()
     * f2 -> Manifest()
     * f3 -> <INSTRUCTIONS>
     * f4 -> Instruction()
     * f5 -> <EOF>
     */
    public void visit(BSProgram n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
        n.f3.accept(this);
        n.f4.accept(this);
        n.f5.accept(this);
    }

    /**
     * f0 -> ( <STATIONARY> ( TypingList() )* Identifier() )*
     */
    public void visit(Stationary n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> ( <MANIFEST> ( TypingList() )* Identifier() )+
     */
    public void visit(Manifest n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> ( <MODULE> Identifier() )*
     */
    public void visit(Module n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> Instruction()
     * | BranchStatement()
     * | WhileStatement()
     */
    public void visit(Statement n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> MixStatement()
     * | SplitStatement()
     * | DrainStatement()
     * | HeatStatement()
     * | DetectStatement()
     * | RepeatStatement()
     * | AssignmentStatement()
     */
    public void visit(Instruction n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <FUNCTION>
     * f1 -> Identifier()
     * f2 -> <LPAREN>
     * f3 -> FormalParameterList()
     * f4 -> <RPAREN>
     * f5 -> ( <COLON> ( TypingList() )* )?
     * f6 -> <LBRACE>
     * f7 -> Statement()
     * f8 -> <LBRACE>
     */
    public void visit(Function n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
        n.f3.accept(this);
        n.f4.accept(this);
        n.f5.accept(this);
        n.f6.accept(this);
        n.f7.accept(this);
        n.f8.accept(this);
    }

    /**
     * f0 -> Type()
     * f1 -> ( TypingRest() )*
     */
    public void visit(TypingList n) {
        n.f0.accept(this);
        n.f1.accept(this);
    }

    /**
     * f0 -> <COMMA>
     * f1 -> Type()
     */
    public void visit(TypingRest n) {
        n.f0.accept(this);
        n.f1.accept(this);
    }

    /**
     * f0 -> FormalParameter()
     * f1 -> ( FormalParameterRest() )*
     */
    public void visit(FormalParameterList n) {
        n.f0.accept(this);
        n.f1.accept(this);
    }

    /**
     * f0 -> TypingList()
     * f1 -> Identifier()
     */
    public void visit(FormalParameter n) {
        n.f0.accept(this);
        n.f1.accept(this);
    }

    /**
     * f0 -> <COMMA>
     * f1 -> FormalParameter()
     */
    public void visit(FormalParameterRest n) {
        n.f0.accept(this);
        n.f1.accept(this);
    }

    /**
     * f0 -> <MIX> PrimaryExpression() <WITH> PrimaryExpression()
     * | <FOR> IntegerLiteral()
     */
    public void visit(MixStatement n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> PrimaryExpression()
     */
    public void visit(SplitStatement n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
        n.f3.accept(this);
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     */
    public void visit(DrainStatement n) {
        n.f0.accept(this);
        n.f1.accept(this);
    }

    /**
     * f0 -> <HEAT> PrimaryExpression() <AT> IntegerLiteral()
     * | <FOR> IntegerLiteral()
     */
    public void visit(HeatStatement n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <DETECT> Identifier() <ON> PrimaryExpression()
     * | <FOR> <INTEGER_LITERAL>
     */
    public void visit(DetectStatement n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> WhileStatement()
     */
    public void visit(RepeatStatement n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     */
    public void visit(AssignmentStatement n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
        n.f3.accept(this);
    }

    /**
     * f0 -> MatLiteral()
     * | NatLiteral()
     * | RealLiteral()
     */
    public void visit(Type n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE_IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE> <LBRACE> Statement() <RBRACE>
     */
    public void visit(BranchStatement n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <REPEAT>
     * f1 -> IntegerLiteral()
     * f2 -> <TIMES>
     * f3 -> <LBRACE>
     * f4 -> Statement()
     * f5 -> <RBRACE>
     */
    public void visit(WhileStatement n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
        n.f3.accept(this);
        n.f4.accept(this);
        n.f5.accept(this);
    }

    /**
     * f0 -> IntegerLiteral()
     * | TrueLiteral()
     * | FalseLiteral()
     * | Identifier()
     * | ParenthesisExpression()
     */
    public void visit(PrimaryExpression n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <INTEGER_LITERAL>
     */
    public void visit(IntegerLiteral n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <NAT>
     */
    public void visit(NatLiteral n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <MAT>
     */
    public void visit(MatLiteral n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <REAL>
     */
    public void visit(RealLiteral n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <TRUE>
     */
    public void visit(TrueLiteral n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <FALSE>
     */
    public void visit(FalseLiteral n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    public void visit(Identifier n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> AndExpression()
     * | LessThanExpression()
     * | LessThanEqualExpression()
     * | GreaterThanExpression()
     * | GreaterThanEqualExpression()
     * | NotEqualExpression()
     * | EqualityExpression()
     * | OrExpression()
     * | PlusExpression()
     * | MinusExpression()
     * | TimesExpression()
     * | PrimaryExpression()
     */
    public void visit(Expression n) {
        n.f0.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <AND>
     * f2 -> PrimaryExpression()
     */
    public void visit(AndExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <LESSTHAN>
     * f2 -> PrimaryExpression()
     */
    public void visit(LessThanExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <LESSTHANEQUAL>
     * f2 -> PrimaryExpression()
     */
    public void visit(LessThanEqualExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <GREATERTHAN>
     * f2 -> PrimaryExpression()
     */
    public void visit(GreaterThanExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <GREATERTHANEQUAL>
     * f2 -> PrimaryExpression()
     */
    public void visit(GreaterThanEqualExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <NOTEQUAL>
     * f2 -> PrimaryExpression()
     */
    public void visit(NotEqualExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <OR>
     * f2 -> PrimaryExpression()
     */
    public void visit(EqualityExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <LESSTHAN>
     * f2 -> PrimaryExpression()
     */
    public void visit(OrExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <ADD>
     * f2 -> PrimaryExpression()
     */
    public void visit(PlusExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <MINUS>
     * f2 -> PrimaryExpression()
     */
    public void visit(MinusExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> PrimaryExpression()
     * f1 -> <MULTIPLY>
     * f2 -> PrimaryExpression()
     */
    public void visit(TimesExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

    /**
     * f0 -> <BANG>
     * f1 -> Expression()
     */
    public void visit(NotExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
    }

    /**
     * f0 -> <LPAREN>
     * f1 -> Expression()
     * f2 -> <RPAREN>
     */
    public void visit(ParenthesisExpression n) {
        n.f0.accept(this);
        n.f1.accept(this);
        n.f2.accept(this);
    }

}
