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
import shared.Step;

/**
 * @created: 11/29/17
 * @since: 0.1
 * @project: MiniComplier
 */
public class BioScript implements Phase {

    public static final Logger logger = LogManager.getLogger(BioScript.class);
    private BSParser parser;
    private CommonConfig config = ConfigFactory.getConfig();
    private Step typeChecker;

    public BioScript() {
    }

    @Override
    public String getName() {
        return "BioScript Parse Strategy";
    }

    @Override
    public Phase run() {
        for (String file : config.getFilesForCompilation()) {
            try (InputStream input = new FileInputStream(file)) {
                this.parser = new BSParser(input);
                input.close();
                // We run the type checking inside the parse.
                try {
                    typeChecker = new BSTypeChecker(this.parser.BSProgram()).run();
                } catch (ParseException e) {
                    logger.error(e);
                }
            } catch (IOException ioe) {
                logger.fatal("Couldn't load the file: " + file);
            }
        }
        return this;
    }

}
