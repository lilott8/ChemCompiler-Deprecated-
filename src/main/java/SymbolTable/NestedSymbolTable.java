package SymbolTable;

import ChemicalInteractions.ChemicalResolution;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * Created by chriscurtis on 10/17/16.
 */
public class NestedSymbolTable{
    protected HashMap<String, ChemicalResolution> __symbols;
    private NestedSymbolTable __parent;

    public NestedSymbolTable() {
        __symbols = new HashMap<String, ChemicalResolution>();
        __parent = null;
    }

    public void put(String key, ChemicalResolution resolution) {
        __symbols.put(resolution.getName(),resolution);
    }
    public void setParent( NestedSymbolTable parent) { __parent = parent; }
    public HashMap<String, ChemicalResolution> getTable() { return __symbols; }
    public ChemicalResolution get(String key){
        return __symbols.get(key);
    }

    public Boolean contains(String substance){
        return __symbols.containsKey(substance);
    }



}
