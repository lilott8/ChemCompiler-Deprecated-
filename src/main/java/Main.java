import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.BasicBlock.DependencySlicedBasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.DominatorTree.DominatorTree;
import CompilerDataStructures.DominatorTree.PostDominatorTree;
import Translators.MFSimSSA.MFSimSSATranslator;
import manager.Benchtop;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import parsing.BioScript.BenchtopParser;

public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);


    public static void main(String[] args) {
        //SimpleMixTest();
        try {

            //logger.info(Main.class.getClassLoader().getResource("Benchmarks/PCRDropletReplacement.json").getPath());


            BenchtopParser.parse(Main.class.getClassLoader().getResource("json_tests/test2.json").getPath());
            //logger.info(Benchtop.INSTANCE.toString());
        }
        catch (Exception e) {
            logger.fatal(e.getMessage());
            logger.fatal(e.getStackTrace());
        }


        try {
            Compiler benchtopCompiler = new Compiler(Benchtop.INSTANCE);


            for(CFG experiment : benchtopCompiler.getExperiments()){
                //logger.debug(experiment.toString());


               //TypeSystemTranslator tst = new TypeSystemTranslator(experiment);
                //tst.toFile("NeurotransmitterSensing.txt");
                //logger.info(tst.toString());
                MFSimSSATranslator mfsimt = new MFSimSSATranslator(experiment);
                mfsimt.toFile("test");
            }

        }
        catch (Exception e ){
            logger.fatal("Exception occured");
            logger.fatal(e.getStackTrace());
        }

       // DominatorTreeTest2();
      //  PostDominatorTreeTest();

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

    public static void DominatorTreeTest2() {
        CFG cfg = new CFG();

        BasicBlock bEntry = cfg.newBasicBlock();
        BasicBlock b1 = cfg.newBasicBlock();
        BasicBlock b2 = cfg.newBasicBlock();
        BasicBlock b3 = cfg.newBasicBlock();
        BasicBlock b4 = cfg.newBasicBlock();
        BasicBlock b5 = cfg.newBasicBlock();
        BasicBlock b6 = cfg.newBasicBlock();
        BasicBlock b7 = cfg.newBasicBlock();
        BasicBlock b8 = cfg.newBasicBlock();
        BasicBlock b9 = cfg.newBasicBlock();
        BasicBlock b10 = cfg.newBasicBlock();
        BasicBlock b11 = cfg.newBasicBlock();
        BasicBlock b12 = cfg.newBasicBlock();
        BasicBlock bExit = cfg.newBasicBlock();

        cfg.addEdge(bEntry,b1);
        cfg.addEdge(bEntry,bExit);
        cfg.addEdge(b1,b2);

        cfg.addEdge(b2,b3);
        cfg.addEdge(b2,b7);

        cfg.addEdge(b3,b4);
        cfg.addEdge(b3,b5);

        cfg.addEdge(b4,b6);
        cfg.addEdge(b5,b6);

        cfg.addEdge(b6,b8);
        cfg.addEdge(b7,b8);

        cfg.addEdge(b8,b9);

        cfg.addEdge(b9,b10);
        cfg.addEdge(b9,b11);

        cfg.addEdge(b10,b11);

        cfg.addEdge(b11,b9);
        cfg.addEdge(b11,b12);

        cfg.addEdge(b12,b2);
        cfg.addEdge(b12,bExit);

        DominatorTree t = new DominatorTree(cfg);
        System.out.println(t);
    }

    public static void PostDominatorTreeTest(){
        CFG cfg = new CFG();

        BasicBlock bEntry = cfg.newBasicBlock();
        BasicBlock b1 = cfg.newBasicBlock();
        BasicBlock b2 = cfg.newBasicBlock();
        BasicBlock b3 = cfg.newBasicBlock();
        BasicBlock b4 = cfg.newBasicBlock();


        BasicBlock bExit = cfg.newBasicBlock();

        cfg.addEdge(bEntry,b1);
        cfg.addEdge(bEntry,bExit);

        cfg.addEdge(b1,b2);
        cfg.addEdge(b1,b3);

        cfg.addEdge(b2,b4);

        cfg.addEdge(b3,b4);

        cfg.addEdge(b4,bExit);

        DominatorTree t = new DominatorTree(cfg);
        PostDominatorTree pt = new PostDominatorTree(cfg);
        System.out.println(t);

        System.out.println(pt);
    }

}
