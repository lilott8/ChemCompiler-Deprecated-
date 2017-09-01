package translators.mfsim;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import compilation.datastructures.cfg.CFG;
import config.TranslateConfig;
import translators.Translator;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSATranslator implements Translator {
    private static final Logger logger = LogManager.getLogger(MFSimSSATranslator.class);


    public class IDGen{
        protected Integer __uniqueIDGen;

        public IDGen(){
            __uniqueIDGen = 0;
        }

        public Integer getNextID() { return __uniqueIDGen++; }

    }
    private IDGen __uniqueIDGen;
    private MFSimSSACFG __controlFLow;

    public MFSimSSATranslator() {}

    private MFSimSSATranslator(CFG controlFlowGraph){
        __uniqueIDGen = new IDGen();
        __controlFLow = new MFSimSSACFG(controlFlowGraph,__uniqueIDGen );
    }

    public void toFile(String output){
        __controlFLow.toFile(output);
    }

    public Translator setConfig(TranslateConfig config) {
        return this;
    }

    public Translator runTranslation(CFG controlFlowGraph) {
        return new MFSimSSATranslator(controlFlowGraph);
    }
}
