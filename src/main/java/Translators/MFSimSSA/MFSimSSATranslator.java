package Translators.MFSimSSA;

import CompilerDataStructures.ControlFlowGraph.CFG;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Created by chriscurtis on 10/28/16.
 */
public class MFSimSSATranslator {
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

    public MFSimSSATranslator(CFG controlFlowGraph){
        __uniqueIDGen = new IDGen();
        __controlFLow = new MFSimSSACFG(controlFlowGraph,__uniqueIDGen );
    }

    public void toFile(String name){
        __controlFLow.toFile(name);
    }


}
