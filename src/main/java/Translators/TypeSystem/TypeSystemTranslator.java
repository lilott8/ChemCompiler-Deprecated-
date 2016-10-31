package Translators.TypeSystem;

import ChemicalInteractions.ChemicalResolution;
import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.CFG;
import ControlFlowGraph.InstructionEdge;
import ControlFlowGraph.InstructionNode;
import executable.instructions.*;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.*;
import java.util.*;

/**
 * Created by chriscurtis on 10/26/16.
 */
public class TypeSystemTranslator implements Serializable{
    public static final Logger logger = LogManager.getLogger(TypeSystemTranslator.class);

    public class TypeSystemSymbolTable implements Serializable {
        private HashMap<String, ChemicalResolution> __symbols;

        public TypeSystemSymbolTable(CFG controlFlowGraph) {
            __symbols = new HashMap<String, ChemicalResolution>();
            for(BasicBlock bb : controlFlowGraph.getBasicBlocks()) {
                for(String symbolName : bb.getSymbolTable().getDefinitionTable().keySet()) {
                    ChemicalResolution symbol = bb.getSymbolTable().get(symbolName);
                    if(! __symbols.containsKey(symbolName))
                        __symbols.put(symbol.getName(),symbol);
                }
            }

            for(ChemicalResolution symbol : controlFlowGraph.getSymbolTable().getTable().values()){
                if(! __symbols.containsKey(symbol.getName()))
                    __symbols.put(symbol.getName(),symbol);
            }

        }

        public String toString() {
            String ret = "";
            for (ChemicalResolution resolution : __symbols.values()) {
                ret += resolution.toString() + '\n';
            }
            return ret;
        }

        public ChemicalResolution getResolution(String symbol) { return __symbols.get(symbol); }
    }


    private List<InstructionNode> __instructions;
    private Map<Integer, Set<Integer>> __children;
    private TypeSystemSymbolTable __table;

    public TypeSystemTranslator(CFG controlFlowGraph)  {
        __instructions = new ArrayList<InstructionNode>();
        __children = new HashMap<Integer, Set<Integer>>();
        __table = new TypeSystemSymbolTable(controlFlowGraph);
       // __controlFlowGraph = controlFlowGraph;

        for(BasicBlock bb : controlFlowGraph.getBasicBlocks()) {
            for (InstructionNode node : bb.getInstructions()) {
                __instructions.add(node);
            }
            for (InstructionEdge edge : bb.getEdges()) {
                if(__children.containsKey(edge.getSource())){
                    __children.get(edge.getSource()).add(edge.getDestination());
                }
                else {
                    Set<Integer> children = new HashSet<Integer>();
                    children.add(edge.getDestination());
                    __children.put(edge.getSource(),children);
                }
            }

            //update symbol table with any definitions:
            for(String resolutionKey: bb.getSymbolTable().getDefinitionTable().keySet()){
            }
        }
    }

    public ChemicalResolution getResolution(String symbol){
        return __table.__symbols.get(symbol);
    }

    public Map<Integer, Set<Integer>> getChildren() {
        return __children;
    }

    public List<InstructionNode> getInstructions() {

        return __instructions;
    }

    public TypeSystemSymbolTable getTable() {
        return __table;
    }

    public String toString(){
        String JSON = "[" + "\n";

        for(Integer i = 0; i < __instructions.size(); ++i) {
            JSON += "\t{\n";
            InstructionNode n = __instructions.get(i);
            JSON += "\t\t\"node\": {\n";
            JSON += "\t\t\t\"id\": " + n.ID() + "," + "\n";

            JSON += "\t\t\t\"instruction\": {\n";
            JSON += "\t\t\t\t\"operation\": \"" + operationType(n.Instruction()) + "\"\n";
            JSON += "\t\t\t},\n";

            JSON += "\t\t\t\"inputs\": {\n";
            Integer maxSize = n.Instruction().getInputs().size();
            Integer aliasIndex = 0;
            for(String alias: n.Instruction().getInputs().keySet()) {
                if (aliasIndex != maxSize) {
                    JSON += "\t\t\t\t\"alias" + aliasIndex++ + "\" : \"" + alias + "\",\n";

                } else {
                    JSON += "\t\t\t\t\"alias" + aliasIndex++ + " \" : \"" + alias + "\"\n";
                }
            }
            JSON += "\t\t\t},\n";

            JSON += "\t\t\t\"edges\": [ \n";

            JSON += "\t\t\t\t";
            if(__children.containsKey(n.ID())) {
                for (Integer childIndex = 0; childIndex < __children.get(n.ID()).size(); ++childIndex) {
                    if (childIndex != __children.get(n.ID()).size() - 1)
                        JSON += __children.get(n.ID()).toArray()[childIndex] + ",";
                    else
                        JSON += __children.get(n.ID()).toArray()[childIndex] + "\n";
                }
            }
            else {
                JSON += "-1\n";
            }
            JSON += "\t\t\t]\n";
            JSON += "\t\t}\n";

            if(i != __instructions.size()-1 )
                JSON += "\t},\n";
            else
                JSON += "\t}\n";

        }


        JSON += __table.toString();


        JSON +="]\n";

        return JSON;



    }

    public static String operationType(Instruction n){
        if(n instanceof Combine)
            return "mix";
        if(n instanceof Heat)
            return "heat";
        if(n instanceof Split)
            return "split";
        if(n instanceof Detect)
            return "detect";
        if(n instanceof Store)
            return "store";
        if(n instanceof Output)
            return "output";

        return "unknown";
    }

    public void toFile(String filename) {
        try {
            FileOutputStream fos = new FileOutputStream(filename);
            ObjectOutputStream oos = new ObjectOutputStream(fos);

            oos.writeObject(this);
        }
        catch (FileNotFoundException fileNotFound){
            logger.fatal("File: " + filename + "not found" );
        }
        catch (IOException object){
            logger.fatal("Object output stream.");
        }

    }

    public static TypeSystemTranslator readFromFile(String filename) {
        try {
            FileInputStream fis = new FileInputStream(filename);
            ObjectInputStream ois = new ObjectInputStream(fis);

            return (TypeSystemTranslator) ois.readObject();
        } catch (FileNotFoundException fileNotFound) {
            logger.fatal("File: " + filename + "not found");
        } catch (IOException object) {
            logger.fatal("Object output stream.");
        } catch (ClassNotFoundException classNotFound) {
            logger.fatal("Class not found.");
        }
        return null;
    }

}

