import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.BasicBlock.DependencySlicedBasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.DominatorTree.DominatorTree;
import CompilerDataStructures.DominatorTree.PostDominatorTree;
import Config.Config;
import Translators.MFSimSSA.MFSimSSATranslator;
import manager.Benchtop;
import parsing.BioScript.BenchtopParser;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.File;
import java.util.ArrayList;
import java.util.List;


public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);

    private static List<String> filesToCompile = new ArrayList<String>();

    public static void main(String[] args) throws Exception {
        // Build the command line parser
        CommandLine cmd;
        CommandLineParser parser = new DefaultParser();

        // parse the command line relative to the options
        cmd = parser.parse(buildOptions(), args);
        initializeEnvironment(cmd);


        // We know that if we reach here, the file exists and is valid.

        //SimpleMixTest();
        try {

            //logger.info(Main.class.getClassLoader().getResource("Benchmarks/PCRDropletReplacement.json").getPath());

            BenchtopParser.parse((String) Config.INSTANCE.get("compile").setting);
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
                if(!((Boolean) Config.INSTANCE.get("tests").setting).booleanValue()) {
                    mfsimt.toFile("test");
                } else {
                    logger.info("We are only compiling we are not generating output");
                }
            }

        }
        catch (Exception e ){
            logger.fatal("Exception occured");
            logger.fatal(e.getStackTrace());
        }

       // DominatorTreeTest2();
      //  PostDominatorTreeTest();

    }

    private static void initializeEnvironment(final CommandLine cmd) throws Exception{
        // see if we asked for help...
        if(cmd.hasOption("help")) {
            HelpFormatter hf = new HelpFormatter();
            hf.printHelp("ChemicalCompiler", buildOptions(), true);
            System.exit(0);
        }


        // See if we have the argument we need.
        if(!cmd.hasOption("compile")) {
            throw new Exception("No input file to compile given.");
        }


        // At this point we know the option 'files' has been
        // provided to the program, so we can safely execute this.
        for (String file : cmd.getOptionValues("compile")) {
            File f = new File(file);
            if (f.exists() && !f.isDirectory()) {
                filesToCompile.add(file);
            }
        }

        // We have to have files to compile...
        if (filesToCompile.isEmpty()) {
            throw new Exception("File(s) not found.");
        }

        Config.INSTANCE.buildConfig(cmd);
        logger.info(Config.INSTANCE.toString());
        // add any initializing statements derived from the command line here.
    }

    /**
     * Builds the command line options needed to run the program
     */
    private static Options buildOptions() {
        Options options = new Options();

        // File to compile
        String desc = "Compile the source file(s)" +
                "\nUsage: -c /path/to/file_to_compile.json";
        options.addOption(Option.builder("c").longOpt("compile")
                .desc(desc).hasArg().required().type(ArrayList.class).argName("compile").build());

        desc = "Test compilation but don't generate output" +
                "\nUsage -t";
        options.addOption(Option.builder("t").longOpt("test").desc(desc).type(Boolean.class).hasArg(false).required(false).argName("tests").build());

        desc = "Place output in file file.  Since only one output file can be specified, it does not make sense to use `-o' when compiling more than one input file" +
                "\n -o /path/to/output/";
        options.addOption(Option.builder("o").longOpt("output").desc(desc).type(String.class).hasArg().required(false).argName("output").build());
        return options;
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
