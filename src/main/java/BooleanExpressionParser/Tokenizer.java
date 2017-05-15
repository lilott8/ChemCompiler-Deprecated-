package BooleanExpressionParser;

import java.util.LinkedList;

@SuppressWarnings("unused")
public class Tokenizer {
    private String expr;
    private LinkedList<Token> tokenList = new LinkedList<>();

    Tokenizer(String boolExpr) {
        this.expr = boolExpr + ";";
        this.tokenList.add(new Token());
        tokenize();
    }

    // Functions
    private void tokenize(){
        Boolean first = Boolean.TRUE;
        for (char i : this.expr.toCharArray()){
            if (first){
                first = Boolean.FALSE;
                this.tokenList.add(new Token(String.valueOf(i)));
                continue;
            }
            this.tokenList.getLast().setValue(this.tokenList.getLast().getValue() + i);
            if (this.tokenList.getLast().isLocked()){
                this.tokenList.add(new Token(String.valueOf(i)));
            }
        }
    }

    private void cleanList(){
        LinkedList<Token> tempList = new LinkedList<>();
        String[] toRemove = {
                "SPACE",
                "ROOT",
                "END"
        };
        Boolean add = Boolean.TRUE;
        for (Token t : this.tokenList){
            add = Boolean.TRUE;
            for (String s : toRemove){
                if (t.getToken().equals(s)){
                    add = Boolean.FALSE;
                }
            }
            if (add){
                tempList.add(t);
            }
        }
        this.tokenList = tempList;
    }

    LinkedList<Token> getList(){
        this.cleanList();
        return this.tokenList;
    }

    String getExpression(){
        return this.expr;
    }

    public String toString(){
        this.cleanList();
        StringBuilder s = new StringBuilder("{");
        for (Token t : this.tokenList){
            s.append(t.toString());
        }
        s.append("}");
        return s.toString();
    }
}


