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
    private BSVisitor symbolTable;
    private BSVisitor typeChecker;
    private BSVisitor irConverter;
    private String file;

    public BioScriptParser(String fileName) {
        this.file = fileName;
        this.symbolTable = new BSSymbolTable();
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
                // logger.info(this.symbolTable);
                if (!this.config.getErrorLevel().disabled()) {
                    this.typeChecker = new BSTypeChecker();
                    program.accept(this.typeChecker);
                    this.typeChecker.run();
                    ((TypeChecker) this.typeChecker).solve();
                } else {
                    logger.error("Type checking has been disabled.");
                }
                this.irConverter = new BSIRConverter();
                program.accept(this.irConverter);
                logger.info(this.irConverter);
            } catch (ParseException e) {
                logger.error(e);
                if (this.config.isDebug()) {
                    e.printStackTrace();
                }
            }
            input.close();
        } catch (IOException ioe) {
            logger.fatal("Couldn't load the file: " + this.file);
        } catch (Exception e) {
            logger.fatal(e.getMessage());
            logger.fatal(e.toString());
            if (this.config.isDebug()) {
                e.printStackTrace();
            }
        }
        return this;
    }

    public String getOutput() {
        return this.irConverter.toString();
    }
}
