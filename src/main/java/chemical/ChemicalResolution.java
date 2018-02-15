package chemical;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

import substance.Chemical;

/**
 * Created by chriscurtis on 10/12/16.
 */
public class ChemicalResolution implements Serializable {
    //AKA the Chemical nesting doll

    private String __name;
    private Boolean __isLiteral;
    private Boolean __isGlobal;
    private Boolean __isStationary;
    private List<Chemical> __chemicalLiterals;
    private List<ChemicalResolution> __chemicalReferences;

    public ChemicalResolution(String name) {
        this.__name = name;
        this.__chemicalReferences = new ArrayList<ChemicalResolution>();
        this.__chemicalLiterals = new ArrayList<Chemical>();
        __isLiteral = false;
        __isGlobal = false;
        __isStationary = false;
    }

    public void setIsLiteral(Boolean isLiteral) { __isLiteral = isLiteral; }
    public void setisGlobal(Boolean isGlobal) { __isGlobal = isGlobal; }
    public void setIsStationary(Boolean isStationary) { __isStationary = isStationary; }

    public void addLiteral(Chemical chemical) { __chemicalLiterals.add(chemical); }
    public void addReference(ChemicalResolution chemicalResolution) {
        __chemicalReferences.add(chemicalResolution);
    }

    public Boolean IsLiteral() {return __isLiteral; }
    public Boolean IsGlobal() { return __isGlobal; }
    public Boolean IsStationary() { return __isStationary; }
    public String getName() { return __name; }
    public List<ChemicalResolution> getReferences() {return __chemicalReferences; }
    public List<Chemical> getLiterals() { return __chemicalLiterals; }

    @Override
    public String toString() {
        if (__isLiteral){
            return __name;
        }

        String ret=this.__name + ": {";

        for (int i =0; i < __chemicalLiterals.size(); ++i) {
//TODO:: create safer chemical tostring function.
            ret += __chemicalLiterals.get(i).getName();

            if (i < __chemicalLiterals.size()-1)
                ret += ", ";
        }

        if(__chemicalReferences.size() >0 && __chemicalLiterals.size() >0)
            ret+=", ";

        for (int i =0; i < __chemicalReferences.size(); ++i) {
            //ret += "{";
            ret += __chemicalReferences.get(i);
//            ret += "}";

            if (i < __chemicalReferences.size()-1)
                ret += ", ";
        }

        ret +="}";
        return ret;
    }
}
