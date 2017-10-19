package compilation.symboltable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import chemicalInteractions.ChemicalResolution;

/**
 * Created by chriscurtis on 10/17/16.
 */
public class NestedSymbolTable{
    // <renamed variable, full resolution>
    protected Map<String, ChemicalResolution> symbols;
    //renamed variable, bb.getID
    protected Map<String,Integer> symbolDefinedIn;
    protected Map<String,Integer> lastUsedIn;

    // oringial name, all renames
    //TODO::
    protected Map<String, List<String>> possibleRenames;
    protected Map<String, String> pointsTo;
    private NestedSymbolTable parent;
    private Integer variableId;


    public void clear(){
        symbolDefinedIn.clear();
        symbols.clear();
        lastUsedIn.clear();
    }

    public NestedSymbolTable() {
        symbols = new HashMap<String, ChemicalResolution>();
        symbolDefinedIn = new HashMap<String, Integer>();
        possibleRenames = new HashMap<String, List<String>>();
        pointsTo = new HashMap<String, String>();
        parent = null;
        variableId =0;
        lastUsedIn = new HashMap<String, Integer>();
    }

    public void put(String key, ChemicalResolution resolution) {
        symbols.put(key,resolution);
    }

    public void put(String key, ChemicalResolution resolution, Integer basicBlockID) {
        symbols.put(key,resolution);
        symbolDefinedIn.put(key,basicBlockID);
    }

    public void addRenamedVariable(String original, String renamed) {
        List<String> renamedVariables;
        if (possibleRenames.containsKey(original))
            renamedVariables = possibleRenames.get(original);
        else
            renamedVariables = new ArrayList<String>();
        renamedVariables.add(renamed);

        pointsTo.put(renamed,original);
        possibleRenames.put(original,renamedVariables);
    }

    public void setParent( NestedSymbolTable parent) { this.parent = parent; }
    public Map<String,String> getPointsTo() { return pointsTo; }
    public List<String> getRenamedVariables(String s) { return possibleRenames.get(s); }


    public Map<String, ChemicalResolution> getTable() { return symbols; }

    public ChemicalResolution get(String key){
        if (symbols.containsKey(key))
            return symbols.get(key);
        if (parent !=null )
            return  parent.get(key);
        return null;
    }

    public Boolean contains(String substance){
        if (symbols.containsKey(substance))
            return true;
        if (parent != null)
            return parent.contains(substance);

        return false;
    }

    public void MarkSymbolInvalid(String symbol) { parent.MarkMySymbolInvalid();}
    protected void MarkMySymbolInvalid() {}
    public void updateLastUsedIn(String symbol, Integer id){
        this.lastUsedIn.put(symbol,id);
    }
    public Integer lastUsedIn (String symbol) {
        return this.lastUsedIn.get(symbol);
    }
    public Map<String, Integer> getUsagedTable() { return this.lastUsedIn;}
    public void clearUsageTable() { lastUsedIn.clear(); }
    public Integer getDefinitionID(String s) { return symbolDefinedIn.get(s);}
    public Map<String,Integer> getDefinitionTable() { return symbolDefinedIn; }

    public void addDefinition(String key, Integer opID) {
        this.symbolDefinedIn.put(key,opID);
    }

    public String getUniqueVariableName(){
        return "v" + (++variableId).toString();
    }
    public NestedSymbolTable getParent() { return parent; }
    public String toString(){
        return this.toString("");
    }
    public String toString(String indentBuffer){
        String ret = "";
        if(parent != null)
            ret+= parent.toString();
        if(possibleRenames !=null && possibleRenames.size()>0) {
            ret += "Renamed Variables: \n";
            for(String key: possibleRenames.keySet()) {
                ret += "\t" + key + ": ";
                for(String rename: possibleRenames.get(key)){
                    ret+= rename + " ";
                }
            }
            ret+='\n';


        }
        if(symbols != null && symbols.size()>0) {
            ret += "Symbols: \n";
            for (ChemicalResolution resolution : symbols.values()) {
                ret += resolution.toString() + '\n';
            }
        }
        return ret;
    }

}
