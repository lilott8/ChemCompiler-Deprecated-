//
// Generated by JTB 1.3.2
//

package parser.ast;

import parser.visitor.GJNoArguVisitor;
import parser.visitor.GJVisitor;
import parser.visitor.GJVoidVisitor;
import parser.visitor.Visitor;

/**
 * The interface which NodeList, NodeListOptional, and NodeSequence
 * implement.
 */
public interface NodeListInterface extends Node {
    public void addNode(Node n);

    public Node elementAt(int i);

    public java.util.Enumeration<Node> elements();

    public int size();

    public void accept(Visitor v);

    public <R, A> R accept(GJVisitor<R, A> v, A argu);

    public <R> R accept(GJNoArguVisitor<R> v);

    public <A> void accept(GJVoidVisitor<A> v, A argu);
}

