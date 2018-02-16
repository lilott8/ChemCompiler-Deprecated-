package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import config.ConfigFactory;
import config.InferenceConfig;
import parser.ast.BSProgram;
import parser.parsing.BSParser;
import parser.parsing.ParseException;
import shared.Phase;

/**
 * @created: 11/29/17
 * @since: 0.1
 * @project: ChemicalComplier
 */
public class BioScriptParser implements Phase {

    public static final Logger logger = LogManager.getLogger(BioScriptParser.class);
    private BSParser parser;
    private InferenceConfig config = ConfigFactory.getConfig();
    private BSTypeChecker typeChecker;
    private BSSymbolTable symbolTable;
    private String file;

    public BioScriptParser(String fileName) {
        this.file = fileName;
        this.symbolTable = new BSSymbolTable();
        this.typeChecker = new BSTypeChecker(this.symbolTable.getSymbolTable());
    }

    @Override
    public String getName() {
        return "BioScriptParser";
    }

    @Override
    public Phase run() {
        try (InputStream input = new FileInputStream(this.file)) {
            this.parser = new BSParser(input);
            try {
                BSProgram program = this.parser.BSProgram();
                program.accept(this.symbolTable);
                logger.info(this.symbolTable);
                //if (!this.config.ignoreWarnings()) {
                // program.accept(this.typeChecker);
                // this.typeChecker.solve();
                //} else {
                logger.warn("Visibility checking is set to ignore warnings.");
                //}
            } catch (ParseException e) {
                logger.error(e);
            }
            input.close();
        } catch (IOException ioe) {
            logger.fatal("Couldn't load the file: " + this.file);
        }
        return this;
    }
}
