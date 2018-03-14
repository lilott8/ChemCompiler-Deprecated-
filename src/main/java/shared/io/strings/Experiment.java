package shared.io.strings;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.awt.*;
import java.awt.datatransfer.StringSelection;
import java.util.List;
import java.util.Map;

import ir.Statement;
import symboltable.SymbolTable;

import static ir.Statement.NL;

/**
 * @created: 3/12/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Experiment implements Stringify {

    public static final Logger logger = LogManager.getLogger(Experiment.class);

    private SymbolTable symbols;
    private Map<String, List<Statement>> statements;

    public Experiment(SymbolTable symbolTable, Map<String, List<Statement>> statements) {
        this.symbols = symbolTable;
        this.statements = statements;
    }

    @Override
    public String toJson() {
        // Open the Object.
        StringBuilder sb = new StringBuilder("{").append(NL);
        // Open the EXPERIMENT.
        sb.append("\"EXPERIMENT\" : {").append(NL);
        for (Map.Entry<String, List<Statement>> entry : this.statements.entrySet()) {
            sb.append("\"NAME\" : \"").append(entry.getKey()).append("\",").append(NL);
            List<Statement> method = entry.getValue();
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

            int x = 0;
            for (Statement s : method) {
                String output = s.toJson();
                if (!StringUtils.isEmpty(output)) {
                    sb.append(output);
                    if (x < method.size()-1) {
                        sb.append(",").append(NL);
                    }
                }
                x++;
            }
            // Closes INSTRUCTIONS.
            sb.append("]").append(NL);
        }
        //sb.append("]").append(NL);
        // Close the EXPERIMENT.
        sb.append("}").append(NL);
        // Close the OBJECT.
        sb.append("}");

        //logger.error("You are copying json to the clipboard!");
        // StringSelection selection = new StringSelection(sb.toString());
        // java.awt.datatransfer.Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
        // clipboard.setContents(selection, selection);
        return sb.toString();
    }
}
