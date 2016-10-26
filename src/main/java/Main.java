import ControlFlowGraph.BasicBlock;
import ControlFlowGraph.CFG;
import DominatorTree.DominatorTree;
import manager.Benchtop;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import parsing.BenchtopParser;

public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);

    public static void main(String[] args) {
        //SimpleMixTest();
        try {
            BenchtopParser.parse(Main.class.getClassLoader().getResource("json_tests/SimpleLoop.json").getPath());
            //logger.info(Benchtop.INSTANCE.toString());
        }
        catch (Exception e) {
            logger.fatal("File not found.");
        }


        try {
            Compiler benchtopCompiler = new Compiler(Benchtop.INSTANCE);
        }
        catch (Exception e ){

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
