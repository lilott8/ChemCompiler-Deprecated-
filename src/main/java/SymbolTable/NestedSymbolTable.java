package SymbolTable;

import ChemicalInteractions.ChemicalResolution;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by chriscurtis on 10/17/16.
 */
public class NestedSymbolTable{
    // <renamed variable, full resolution>
    protected HashMap<String, ChemicalResolution> __symbols;
    //renamed variable, bb.getID
    protected HashMap<String,Integer> __symbolDefinedIn;
    protected HashMap<String,Integer> __lastUsedIn;

    // oringial name, all renames
    //TODO::
    protected HashMap<String, List<String>> __possibleRenames;
    protected HashMap<String, String> __pointsTo;
    private NestedSymbolTable __parent;
    private Integer __varaibleID;


    public void clear(){
        __symbolDefinedIn.clear();
        __symbols.clear();
        __lastUsedIn.clear();
    }

    public NestedSymbolTable() {
        __symbols = new HashMap<String, ChemicalResolution>();
        __symbolDefinedIn = new HashMap<String, Integer>();
        __possibleRenames = new HashMap<String, List<String>>();
        __pointsTo = new HashMap<String, String>();
        __parent = null;
        __varaibleID  =0;
        __lastUsedIn = new HashMap<String, Integer>();
    }

    public void put(String key, ChemicalResolution resolution) {
        __symbols.put(key,resolution);
    }

    public void put(String key, ChemicalResolution resolution, Integer basicBlockID) {
        __symbols.put(key,resolution);
        __symbolDefinedIn.put(key,basicBlockID);
    }

    public void addRenamedVariable(String original, String renamed) {
        List<String> renamedVariables;
        if (__possibleRenames.containsKey(original))
            renamedVariables = __possibleRenames.get(original);
        else
            renamedVariables = new ArrayList<String>();
        renamedVariables.add(renamed);

        __pointsTo.put(renamed,original);
        __possibleRenames.put(original,renamedVariables);
    }

    public void setParent( NestedSymbolTable parent) { __parent = parent; }
    public HashMap<String,String> getPointsTo() { return __pointsTo; }
    public List<String> getRenamedVariables(String s) { return __possibleRenames.get(s); }


    public HashMap<String, ChemicalResolution> getTable() { return __symbols; }

    public ChemicalResolution get(String key){
        if (__symbols.containsKey(key))
            return __symbols.get(key);
        if (__parent!=null )
            return  __parent.get(key);
        return null;
    }

    public Boolean contains(String substance){
        if (__symbols.containsKey(substance))
            return true;
        if (__parent!= null)
            return __parent.contains(substance);

        return false;
    }

    public void MarkSymbolInvalid(String symbol) { __parent.MarkMySymbolInvalid();}
    protected void MarkMySymbolInvalid() {}
    public void updateLastUsedIn(String symbol, Integer id){
        this.__lastUsedIn.put(symbol,id);
    }
    public Integer lastUsedIn (String symbol) {
        return this.__lastUsedIn.get(symbol);
    }
    public Map<String, Integer> getUsagedTable() { return this.__lastUsedIn;}
    public void clearUsageTable() { __lastUsedIn.clear(); }
    public Integer getDefinitionID(String s) { return __symbolDefinedIn.get(s);}
    public Map<String,Integer> getDefinitionTable() { return __symbolDefinedIn; }

    public void addDefinition(String key, Integer opID) {
        this.__symbolDefinedIn.put(key,opID);
    }

    public String getUniqueVariableName(){
        return "v" + (++__varaibleID).toString();
    }
    public NestedSymbolTable getParent() { return __parent; }
    public String toString(){
        return this.toString("");
    }
    public String toString(String indentBuffer){
        String ret = "";
        if(__parent!= null)
            ret+= __parent.toString();
        if(__possibleRenames!=null && __possibleRenames.size()>0) {
            ret += "Renamed Variables: \n";
            for(String key: __possibleRenames.keySet()) {
                ret += "\t" + key + ": ";
                for(String rename: __possibleRenames.get(key)){
                    ret+= rename + " ";
                }
            }
            ret+='\n';


        }
        if(__symbols!= null && __symbols.size()>0) {
            ret += "Symbols: \n";
            for (ChemicalResolution resolution : __symbols.values()) {
                ret += resolution.toString() + '\n';
            }
        }
        return ret;
    }

}
