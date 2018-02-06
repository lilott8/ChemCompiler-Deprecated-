package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import config.CommonConfig;
import config.ConfigFactory;
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
    private CommonConfig config = ConfigFactory.getConfig();
    private TypeChecker typeChecker;
    private SymbolTable symbolTable;
    private String file;

    public BioScriptParser(String fileName) {
        this.file = fileName;
    }

    @Override
    public String getName() {
        return "BioScriptParser";
    }

    @Override
    public Phase run() {
        try (InputStream input = new FileInputStream(this.file)) {
            this.parser = new BSParser(input);
            // We run the type checking inside the parse.
            try {
                this.parser.BSProgram();
                this.symbolTable = ((SymbolTable) new BSSymbolTable((this.parser.BSProgram())).run());
                this.typeChecker = ((TypeChecker) new BSTypeChecker(this.parser.BSProgram()).run());
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
