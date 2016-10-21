package SymbolTable;

import ChemicalInteractions.ChemicalResolution;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * Created by chriscurtis on 10/17/16.
 */
public class NestedSymbolTable{
    // <renamed variable, full resolution>
    protected HashMap<String, ChemicalResolution> __symbols;
    //renamed variable, bb.ID
    protected HashMap<String,Integer> __symbolDefinedIn;
    // oringial name, all renames
    //TODO::
    protected HashMap<String, List<String>> __possibleRenames;
    protected HashMap<String, String> __pointsTo;
    private NestedSymbolTable __parent;
    private Integer __varaibleID;




    public NestedSymbolTable() {
        __symbols = new HashMap<String, ChemicalResolution>();
        __symbolDefinedIn = new HashMap<String, Integer>();
        __possibleRenames = new HashMap<String, List<String>>();
        __pointsTo = new HashMap<String, String>();
        __parent = null;
        __varaibleID  =0;
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
        return __symbols.get(key);
    }

    public Boolean contains(String substance){
        return __symbols.containsKey(substance);
    }

    public String getUniqueVariableName(){
        return "v" + (++__varaibleID).toString();
    }

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
