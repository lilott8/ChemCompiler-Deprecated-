import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.CFG;
import DominatorTree.DominatorTree;
import Translators.MFSimSSA.MFSimSSATranslator;
import Translators.TypeSystem.TypeSystemTranslator;
import manager.Benchtop;
import manager.TypeSystem;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import parsing.BenchtopParser;

public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);

    public static void main(String[] args) {
        //SimpleMixTest();
        try {

            //logger.info(Main.class.getClassLoader().getResource("Benchmarks/PCRDropletReplacement.json").getPath());


            BenchtopParser.parse(Main.class.getClassLoader().getResource("Benchmarks/MorphineELISA.json").getPath());
            //logger.info(Benchtop.INSTANCE.toString());
        }
        catch (Exception e) {
            logger.fatal(e.getMessage());
            logger.fatal(e.getStackTrace());
        }


        try {
            Compiler benchtopCompiler = new Compiler(Benchtop.INSTANCE);

            for(CFG experiment : benchtopCompiler.getExperiments()){
                logger.debug(experiment.toString());

                //TypeSystemTranslator tst = new TypeSystemTranslator(experiment);
                MFSimSSATranslator mfsimt = new MFSimSSATranslator(experiment);
                mfsimt.toFile("MorphineELISA");
            }

        }
        catch (Exception e ){
            logger.fatal("Exception occured");
            logger.fatal(e.getStackTrace());
        }

        //DominatorTreeTest();

    }

    public static void DominatorTreeTest() {
        CFG cfg = new CFG();

        BasicBlock b1 = cfg.newBasicBlock();
        BasicBlock b2 = cfg.newBasicBlock();
        BasicBlock b3 = cfg.newBasicBlock();
        BasicBlock b4 = cfg.newBasicBlock();
        BasicBlock b5 = cfg.newBasicBlock();
        BasicBlock b6 = cfg.newBasicBlock();
        BasicBlock b7 = cfg.newBasicBlock();
        BasicBlock b8 = cfg.newBasicBlock();


        cfg.addEdge(b1,b2);
        cfg.addEdge(b2,b3);
        cfg.addEdge(b2,b4);

        cfg.addEdge(b3,b5);
        cfg.addEdge(b4,b5);

        cfg.addEdge(b5,b6);
        cfg.addEdge(b6,b7);
        cfg.addEdge(b7,b6);
        cfg.addEdge(b6,b8);

        cfg.addEdge(b8,b2);


        DominatorTree t = new DominatorTree(cfg);
        logger.info(t);
    }


}
