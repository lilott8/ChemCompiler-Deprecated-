package shared.io.strings;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jgrapht.Graph;
import org.jgrapht.traverse.DepthFirstIterator;

import java.awt.*;
import java.awt.datatransfer.StringSelection;
import java.util.Map;

import ir.graph.BlockGraph;
import ir.graph.Edge;
import ir.statements.Statement;
import symboltable.SymbolTable;

import static ir.statements.Statement.NL;

/**
 * @created: 3/12/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Experiment implements Stringify {

    public static final Logger logger = LogManager.getLogger(Experiment.class);

    private SymbolTable symbols;
    private Map<String, BlockGraph> graphs;

    public Experiment(SymbolTable symbolTable, Map<String, BlockGraph> graphs) {
        this.symbols = symbolTable;
        this.graphs = graphs;
    }

    @Override
    public String toJson() {
        // Open the Object.
        StringBuilder sb = new StringBuilder("{").append(NL);
        // Open the EXPERIMENT.
        sb.append("\"EXPERIMENT\" : {").append(NL);
        for (Map.Entry<String, BlockGraph> entry : this.graphs.entrySet()) {
            sb.append("\"NAME\" : \"").append(entry.getKey()).append("\",").append(NL);
            Graph<Statement, Edge> graph = entry.getValue().getGraph();
            DepthFirstIterator<Statement, Edge> iterator = new DepthFirstIterator<>(graph);
            Statement statement;

            // Open INPUTS.
            sb.append("\"INPUTS\" : [").append(NL);
            for (int x = 0; x < this.symbols.getInputs().size(); x++) {
                sb.append("{").append(NL);
                sb.append(this.symbols.getInputs().get(x).buildDeclaration());
                sb.append(NL).append("}").append(NL);
                if (x < this.symbols.getInputs().size() - 1) {
                    sb.append(",").append(NL);
                }
            }
            // Closes INPUTS.
            sb.append("],").append(NL);
            // Open INSTRUCTIONS.
            sb.append("\"INSTRUCTIONS\" : [").append(NL);
            while (iterator.hasNext()) {
                statement = iterator.next();
                String output = statement.toJson();
                if (!StringUtils.isEmpty(output)) {
                    sb.append(output);
                    if (iterator.hasNext()) {
                        sb.append(",").append(NL);
                    }
                }
            }
            // Closes INSTRUCTIONS.
            sb.append("]").append(NL);
        }
        //sb.append("]").append(NL);
        // Close the EXPERIMENT.
        sb.append("}").append(NL);
        // Close the OBJECT.
        sb.append("}");

        logger.error("You are copying json to the clipboard!");
        StringSelection selection = new StringSelection(sb.toString());
        java.awt.datatransfer.Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
        clipboard.setContents(selection, selection);
        return sb.toString();
    }
}
