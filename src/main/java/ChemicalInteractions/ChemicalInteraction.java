package ChemicalInteractions;

import executable.instructions.Combine;
import executable.instructions.Heat;
import substance.Chemical;
import substance.Property;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/**
 * Created by chriscurtis on 10/4/16.
 */
public class ChemicalInteraction implements Serializable {


    public enum Operation {DISPENSE, DETECT, HEAT, MIX, SPLIT, STORE, OUTPUT}


    private Integer __ID;
    private Operation __type;
    private List<Chemical> __chemicals;
    private List<Property> __properties;

    public ChemicalInteraction(Integer id, Operation operationType)
    {
        __ID = id;
        __type = operationType;
        __chemicals = new ArrayList<Chemical>();
        __properties = new ArrayList<Property>();
    }

    public void addChemical (Chemical chemical) { __chemicals.add(chemical); }
    public void addProperty (Property property) { __properties.add(property); }

    public List<Property> getProperties() { return __properties; }
    public List<Chemical> getChemicals() { return __chemicals; }
    public Integer getID() { return __ID; }

    public Boolean isDispense() { return __type == Operation.DISPENSE; }
    public Boolean isDetect() { return __type == Operation.DETECT; }
    public Boolean isHeat() { return __type == Operation.HEAT; }
    public Boolean isMix() { return __type == Operation.MIX; }
    public Boolean isSplit() { return __type == Operation.SPLIT; }
    public Boolean isStore() { return __type == Operation.STORE; }
    public Boolean isOutput() { return __type == Operation.OUTPUT; }
}
