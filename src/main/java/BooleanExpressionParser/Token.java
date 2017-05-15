package BooleanExpressionParser;

import java.util.LinkedList;
import java.util.Queue;

public @SuppressWarnings("unused")
class Token  {
    // Constants
    private static final PatternPair[] validTokens = {
            new PatternPair("END","^;$"),
            new PatternPair("SPACE","^\\s+$"),
            new PatternPair("TRUE","^true$"),
            new PatternPair("FALSE","^false$"),
            new PatternPair("IDENTIFIER","^[a-zA-Z0-9]$"),
            new PatternPair("AND","^&&$|^&$"),
            new PatternPair("OR","^\\|\\|$|^\\|$"),
            new PatternPair("NOT","^!$"),
            new PatternPair("LT","^<$"),
            new PatternPair("LTE","^<=$"),
            new PatternPair("GT", "^>$"),
            new PatternPair("GTE","^>=$"),
            new PatternPair("EQ","^==$|^=$"),
            new PatternPair("NEQ","^!=$"),
            new PatternPair("L_PAREN","^\\($"),
            new PatternPair("R_PAREN","^\\)$")
    };
    private static final PatternPair[] keywords = {
            new PatternPair("TRUE", "true"),
            new PatternPair("FALSE", "false")
    };
    private static final String identifier_halts = "(.*)[!=><()&|;]$";

    // Variables
    private String value;
    private Boolean locked;
    private Queue<String> potentialTokens;

    // Constructor
    Token(String value){
        this.value = value;
        this.potentialTokens = new LinkedList<>();
        this.locked = Boolean.FALSE;
        check_tokens();
    }
    Token(){
        this.potentialTokens = new LinkedList<>();
        this.value = "";
        this.locked = Boolean.TRUE;
        this.potentialTokens.add("ROOT");
    }

    // Functions
    private void check_tokens(){
        Queue<String> newTokens = new LinkedList<>();
        for (PatternPair i : validTokens){
            if (this.value.matches(i.getPattern())){
                newTokens.add(i.getToken());
            }
        }
        if (newTokens.isEmpty()){
            this.locked = Boolean.TRUE;
            this.value = this.value.substring(0, this.value.length() - 1);
        }else{
            this.potentialTokens = newTokens;
        }
    }
    private void check_identifier(){
        if (this.value.matches(identifier_halts)){
            remove_last_char();
            while (this.value.charAt(this.value.length()-1) == ' '){
                remove_last_char();
            }
            this.locked = Boolean.TRUE;
            // Check if IDENTIFIER is actually a KEYWORD
            for (PatternPair i : keywords){
                if (this.value.equals(i.getPattern())){
                    this.potentialTokens.remove();
                    this.potentialTokens.add(i.getToken());
                }
            }
        }
    }
    private void remove_last_char(){
        this.value = this.value.substring(0, this.value.length() - 1);
    }

    // Mutators/Accesors
    String getToken(){
        return this.potentialTokens.peek();
    }
    String getValue(){
        return this.value;
    }
    void setValue(String value){
        if (!this.locked){
            this.value = value;
            if (this.potentialTokens.peek().equals("IDENTIFIER")){
                check_identifier();
            }else{
                check_tokens();
            }
        }
    }
    Boolean isLocked(){
        return this.locked;
    }
    public String toString(){
        return "\"" + this.getToken() + "\": \"" + this.getValue() + "\"";
    }
    public String toString(String s){
        return "\"" + this.getToken() + s + "\": \"" + this.getValue() + "\"";
    }
}
