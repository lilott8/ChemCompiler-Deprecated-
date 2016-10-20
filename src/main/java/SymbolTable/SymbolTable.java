package SymbolTable;

import ChemicalInteractions.ChemicalResolution;

import java.util.HashMap;

/**
 * Created by chriscurtis on 10/17/16.
 */
public class SymbolTable {
    protected HashMap<String, ChemicalResolution> __symbol;

    public SymbolTable() {
        __symbol = new HashMap<String, ChemicalResolution>();
    }

}
