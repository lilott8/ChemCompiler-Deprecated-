package compiler;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import compilation.datastructures.basicblock.BasicBlock;
import compilation.datastructures.cfg.CFG;
import compilation.datastructures.dominatortree.DominatorTree;
import compilation.datastructures.dominatortree.PostDominatorTree;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TreeTest {

    private static Logger logger = LogManager.getLogger(TreeTest.class);

    // @Test
    public void DominatorTreeTest() {
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
        // TODO: add asserts.
    }

    // @Test
    public void DominatorTreeTest2() {
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
        logger.info(t);
        // TODO: add asserts.
    }

    // @Test
    public void PostDominatorTreeTest(){
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
        logger.info(t);
        // TODO: add asserts.

        logger.info(pt);
        // TODO: add asserts.
    }
}
