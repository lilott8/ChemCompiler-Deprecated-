package translators.mfsim;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import compilation.datastructures.cfg.CFG;
import config.CommonConfig;
import config.Config;
import config.TranslateConfig;
import translators.Translator;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSATranslator implements Translator {
    private static final Logger logger = LogManager.getLogger(MFSimSSATranslator.class);


    private IDGen uniqueIDGen;
    private MFSimSSACFG controlFLow;
    private CommonConfig config;

    private MFSimSSATranslator(CFG controlFlowGraph) {
        uniqueIDGen = new IDGen();
        controlFLow = new MFSimSSACFG(controlFlowGraph, uniqueIDGen);
    }

    public MFSimSSATranslator() {
    }

    public void toFile(String output) {
        controlFLow.toFile(output);
    }

    public void toFile() {
        this.toFile(this.config.getOutputDir() + "output");
    }

    public Translator setConfig(TranslateConfig config) {
        this.config = config;
        return this;
    }

    public Translator runTranslation(CFG controlFlowGraph) {
        return new MFSimSSATranslator(controlFlowGraph);
    }

    public class IDGen {
        protected Integer uniqueIDGen;

        public IDGen() {
            uniqueIDGen = 0;
        }

        public Integer getNextID() {
            return uniqueIDGen++;
        }

    }
}
