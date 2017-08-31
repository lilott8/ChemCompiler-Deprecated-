package Translators;

import org.apache.commons.lang3.StringUtils;

import java.util.HashMap;
import java.util.Map;

import CompilerDataStructures.ControlFlowGraph.CFG;
import config.TranslateConfig;
import shared.Facade;
import Translators.MFSimSSA.MFSimSSATranslator;
import Translators.TypeSystem.TypeSystemTranslator;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TranslatorFacade implements Facade {

    public enum TRANSLATORS {
        MFSIM, TYPESYSTEM, NONE;

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

    private TranslateConfig config;
    private Map<TRANSLATORS, Translator> translators = new HashMap<TRANSLATORS, Translator>();
    private CFG controlFlowGraph;

    public TranslatorFacade(TranslateConfig config, CFG cfg) {
        this.controlFlowGraph = cfg;
        this.config = config;

        for(Map.Entry<String, Translator> entry: this.config.getAllTranslations().entrySet()) {
            TRANSLATORS t = TRANSLATORS.valueOf(StringUtils.upperCase(entry.getKey()));
            this.translators.put(t, TRANSLATORS.getTranslator(t));
        }
    }

    public void start() {
        for (Map.Entry<TRANSLATORS, Translator> t : this.translators.entrySet()) {
            t.getValue().runTranslation(this.controlFlowGraph).toFile(this.config.getOutputDir() + this.controlFlowGraph.getID());
        }
    }
}
