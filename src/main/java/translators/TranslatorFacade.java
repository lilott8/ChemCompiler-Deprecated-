package translators;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.Map;

import compilation.datastructures.cfg.CFG;
import config.TranslateConfig;
import shared.Facade;
import translators.mfsim.MFSimSSATranslator;
import translators.typesystem.TypeSystemTranslator;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TranslatorFacade implements Facade {

    public static final Logger logger = LogManager.getLogger(TranslatorFacade.class);

    private TranslateConfig config;
    private Map<TRANSLATORS, Translator> translators = new HashMap<TRANSLATORS, Translator>();
    private CFG controlFlowGraph;

    public TranslatorFacade(TranslateConfig config, CFG cfg) {
        this.controlFlowGraph = cfg;
        this.config = config;

        for (TRANSLATORS entry : this.config.getAllTranslations()) {
            this.translators.put(entry, TRANSLATORS.getTranslator(entry));
        }
    }

    public void start() {
        for (Map.Entry<TRANSLATORS, Translator> t : this.translators.entrySet()) {
            logger.info("Running transform: " + t.getKey() + ".");
            t.getValue().runTranslation(this.controlFlowGraph).toFile(this.config.getOutputDir());
            logger.info("Done running: " + t.getKey() + " transform.");

        }
    }

    public enum TRANSLATORS {
        MFSIM, TYPESYSTEM, MICRODROP, NONE;

        public static Translator getTranslator(TRANSLATORS t) {
            switch (t) {
                default:
                case MFSIM:
                    return new MFSimSSATranslator();
                case TYPESYSTEM:
                    return new TypeSystemTranslator();
            }
        }
    }
}
