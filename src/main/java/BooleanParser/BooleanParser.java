package BooleanParser;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

@SuppressWarnings("unused")
public class BooleanParser {
    // Constants
    private static final CFGPair[] types = {
        new CFGPair("expr", new LinkedList<>(Collections.singletonList("EXPR"))),
        new CFGPair("node", new LinkedList<>(Arrays.asList("IDENTIFIER", "TRUE", "FALSE"))),
        new CFGPair("relation_op", new LinkedList<>(Arrays.asList("LT", "LTE", "GT", "GTE", "EQ", "NEQ"))),
        new CFGPair("logical_op", new LinkedList<>(Arrays.asList("AND","OR"))),
        new CFGPair("not", new LinkedList<>(Collections.singletonList("NOT"))),
        new CFGPair("l_paren", new LinkedList<>(Collections.singletonList("L_PAREN"))),
        new CFGPair("r_paren", new LinkedList<>(Collections.singletonList("R_PAREN")))
    };
    private static final CFGPair[] cfg = {
        new CFGPair("not", new LinkedList<>(Arrays.asList("not", "expr"))),
        new CFGPair("conn", new LinkedList<>(Arrays.asList("node", "relation_op", "node"))),
        new CFGPair("conn", new LinkedList<>(Arrays.asList("expr", "logical_op", "expr"))),
        new CFGPair("paren", new LinkedList<>(Arrays.asList("l_paren", "node", "r_paren"))),
        new CFGPair("paren", new LinkedList<>(Arrays.asList("l_paren", "expr", "r_paren"))),
    };

    //Variables
    private LinkedList<Token> input = new LinkedList<>();
    private LinkedList<BooleanExpr> stack = new LinkedList<>();
    private LinkedList<BooleanExpr> buffer = new LinkedList<>();
    private BooleanExpr root = null;
    private String expr;

    // Constructors
    BooleanParser(Tokenizer t){
        this.expr = t.getExpression();
        this.input = t.getList();
        parse();
    }
    BooleanParser(String expr){
        this.expr = expr;
        this.input = new Tokenizer(expr).getList();
        parse();
    }

    // Methods
    private void parse(){
        while (this.input.size() > 0){
            this.stack.add(new TokenExpr(this.input.removeFirst()));
            this.reduce();
        }
    }

    private void reduce(){
        Boolean canReduce = Boolean.TRUE;
        while (canReduce){
            this.buffer.clear();
            canReduce = Boolean.FALSE;
            int count = 3;
            while (this.stack.size() > 0 && count > 0){
                this.buffer.addFirst(this.stack.removeLast());
                count--;
            }
            // Collect the tokens by Type
            LinkedList<String> buffer_types = new LinkedList<>();
            for (BooleanExpr b : this.buffer){
                for (CFGPair p : types){
                    for (String s : p.getPattern()){
                        if (b.getToken().equals(s)){
                            buffer_types.addLast(p.getToken());
                        }
                    }
                }
            }
            // Check CFG table for reductions
            for (CFGPair p : cfg){
                if (p.getPattern().equals(buffer_types) || (buffer_types.size() > 2 && this.listEquals(buffer_types.subList(1,3),p.getPattern()))){
                    canReduce = Boolean.TRUE;
                    switch (p.getToken()){
                        case "not":
                            this.stack.add(this.buffer.removeFirst());
                            this.buffer.removeFirst();
                            this.stack.add(new NotExpr(this.buffer.removeFirst()));
                            break;
                        case "conn":
                            BooleanExpr left = this.buffer.removeFirst();
                            BooleanExpr conn = this.buffer.removeFirst();
                            BooleanExpr right = this.buffer.removeFirst();
                            this.stack.add(new FullExpr(left, conn, right));
                            break;
                        case "paren":
                            this.buffer.removeFirst();
                            this.stack.add(this.buffer.removeFirst());
                            break;
                    }
                }
            }
            // If Reducing didn't happen add unused buffer back to the stack
            if (!canReduce){
                this.stack.addAll(this.buffer);
            }
        }
    }

    private Boolean listEquals(List<String> l1, LinkedList<String> l2){
        if( l1.size() != l2.size() ){
            return Boolean.FALSE;
        }
        for(int i=0; i<l2.size(); i++){
            if(!(l1.get(i).equals(l2.get(i))))
                return Boolean.FALSE;
        }
        return Boolean.TRUE;
    }

    // Public Methods
    public String toString(){
        return "{ \"TEXT\": \"" + this.expr + "\", " + this.stack.getFirst().toString() + "}";
    }

    public BooleanExpr getRoot(){
        return this.stack.getFirst();
    }
}


@SuppressWarnings("unused")
abstract class BooleanExpr {
    String getToken(){
        return "EXPR";
    }
    abstract BooleanExpr left();
    abstract BooleanExpr right();
    abstract BooleanExpr conn();
    abstract String getValue();
    public abstract String toString(String s);
}

@SuppressWarnings("unused")
class NotExpr extends BooleanExpr {
    private BooleanExpr expr;
    NotExpr(BooleanExpr expr){
        this.expr = expr;
    }
    NotExpr(Token token){
        this.expr = new TokenExpr(token);
    }
    String getValue(){
        return " NOT " + expr.getValue();
    }
    BooleanExpr left(){
        return this.expr;
    }
    BooleanExpr right(){
        return this.expr;
    }
    BooleanExpr conn(){
        return new TokenExpr(new Token("!"));
    }
    public String toString(){
        return "\"EXPR\": { \"NOT\":\"!\", " + expr.toString() + "}";
    }
    public String toString(String s){
        return "\"EXPR" + s + "\": { \"NOT\":\"!\", " + expr.toString() + "}";
    }
}

@SuppressWarnings("unused")
class TokenExpr extends BooleanExpr {
    private Token token;
    TokenExpr(Token t){
        this.token = t;
    }
    BooleanExpr conn(){
        return null;
    }
    BooleanExpr left() {
        return null;
    }
    BooleanExpr right() {
        return null;
    }
    String getValue(){
        return token.getValue();
    }
    String getToken(){
        return token.getToken();
    }
    public String toString(){
        return token.toString();
    }

    public String toString(String s){
        return token.toString(s);
    }
}

@SuppressWarnings("unused")
class FullExpr extends BooleanExpr {
    private BooleanExpr left, right, connector;

    BooleanExpr conn(){
        return this.connector;
    }
    BooleanExpr left(){
        return this.left;
    }
    BooleanExpr right(){
        return this.right;
    }
    String getValue(){
        return " " + left.getValue() + " " + connector.getToken() + " " + right.getValue();
    }
    public String toString(){
        return "\"EXPR\": {" + left.toString("_L") +
                ", " + connector.toString() +
                ", " + right.toString("_R") + "}";
    }
    public String toString(String s){
        return "\"EXPR" + s + "\": {" + left.toString("_L") +
                ", " + connector.toString() +
                ", " + right.toString("_R") + "}";
    }

    // Constructors
    FullExpr(BooleanExpr left, BooleanExpr conn, BooleanExpr right){
        this.left = left;
        this.right = right;
        this.connector = conn;
    }

}


class PatternPair {
    private String token;
    private String pattern;

    PatternPair(String token, String pattern){
        this.token = token;
        this.pattern = pattern;
    }

    String getToken(){
        return this.token;
    }

    String getPattern(){
        return this.pattern;
    }
}

@SuppressWarnings("unused")
class CFGPair {
    private String token;
    private LinkedList<String> pattern;

    CFGPair(String token, LinkedList<String> pattern){
        this.token = token;
        this.pattern = pattern;
    }

    String getToken(){
        return this.token;
    }

    LinkedList<String> getPattern(){
        return this.pattern;
    }

    Boolean contains(String test){
        for (String s : this.pattern){
            if(s.equals(test)){
                return Boolean.TRUE;
            }
        }
        return Boolean.FALSE;
    }

    Boolean matches(LinkedList<String> test){
        if(this.pattern.equals(test))
            return Boolean.TRUE;
        return Boolean.FALSE;
    }
}


