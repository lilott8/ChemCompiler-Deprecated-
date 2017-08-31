import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;

import CompilerDataStructures.BasicBlock.BasicBlock;
import CompilerDataStructures.ControlFlowGraph.CFG;
import CompilerDataStructures.DominatorTree.DominatorTree;
import CompilerDataStructures.DominatorTree.PostDominatorTree;
import config.Config;
import phases.PhaseFacade;
import shared.Facade;
import Translators.TranslatorFacade;
import manager.Benchtop;
import parsing.BioScript.BenchtopParser;


public class Main {
    public static final Logger logger = LogManager.getLogger(Main.class);

    public static void main(String[] args) throws Exception {
        // Build the command line parser
        CommandLine cmd;
        CommandLineParser parser = new DefaultParser();

        // parse the command line relative to the options
        cmd = parser.parse(buildOptions(), args);
        initializeEnvironment(cmd);

        if (Config.INSTANCE.isDebug()) {
            logger.info("You are in test mode");
        }

        //SimpleMixTest();
        try {
            for(String file : Config.INSTANCE.getFilesForCompilation()) {
                logger.trace(file);
                BenchtopParser.parse(file);
            }
            //logger.info(Benchtop.INSTANCE.toString());
        }
        catch (Exception e) {
            logger.fatal(e.getMessage());
            //e.printStackTrace();
            logger.fatal("Exception: ", e);
        }


        try {
            Compiler benchtopCompiler = new Compiler(Benchtop.INSTANCE);
            benchtopCompiler.compile();

            for(CFG experiment : benchtopCompiler.getExperiments()){
                //logger.debug(experiment.toString());
                //TypeSystemTranslator tst = new TypeSystemTranslator(experiment);
                //tst.toFile("NeurotransmitterSensing.txt");
                //logger.info(tst.toString());
                if (Config.INSTANCE.translationsEnabled()) {
                    Facade translator = new TranslatorFacade(Config.INSTANCE, experiment);
                    translator.start();
                }
                //if (config.INSTANCE.translationsEnabled() && config.INSTANCE.translationEnabled(config.TRANSLATORS.MFSIM)) {
                //    config.INSTANCE.getTranslationByName(config.TRANSLATORS.MFSIM).runTranslation(experiment).toFile(config.INSTANCE.getOuptutDir() + "test");
                    //Translator mfsimt = new MFSimSSATranslator().runTranslation(experiment);
                    //mfsimt.toFile(config.INSTANCE.getOuptutDir());
                //}

                //if (config.INSTANCE.phasesEnabled() &&config.INSTANCE.phaseEnabled(config.PHASES.INFERENCE)) {
                //   config.INSTANCE.getPhaseByName(config.PHASES.INFERENCE).runPhase();
                //}
                if(Config.INSTANCE.phasesEnabled()) {
                 Facade phase = new PhaseFacade(Config.INSTANCE, experiment);
                 phase.start();
                }
            }

        }
        catch (Exception e ){
            logger.fatal("Exception occurred");
            e.getStackTrace();
            logger.fatal("Stack Trace:", e.getStackTrace());
        }

        if (Config.INSTANCE.isDebug()) {
            DominatorTreeTest();
            DominatorTreeTest2();
            PostDominatorTreeTest();
        }
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

        // If we have a translator we must also have output.
        if ((cmd.hasOption("translate") && !cmd.hasOption("output")) || cmd.hasOption("output") && !cmd.hasOption("translate")) {
            throw new Exception("If you provide a translation or an output, the other must accompany.");
        }

        if ((cmd.hasOption("clean") && !cmd.hasOption("output"))) {
            throw new Exception("Attempting to clean output directory, but no directory supplied.");
        }

        // initialize our config object.
        Config.INSTANCE.buildConfig(cmd);

        // add any initializing statements derived from the command line here.
        if(Config.INSTANCE.getFilesForCompilation().size() == 0) {
            throw new Exception("We have no valid files for input");
        }
    }

    /**
     * Builds the command line options needed to run the program
     */
    private static Options buildOptions() {
        Options options = new Options();

        // File(s) to compile
        String desc = "Compile the source file(s)" +
                "\nUsage: -c /path/to/file_to_compile.json";
        options.addOption(Option.builder("c").longOpt("compile")
                .desc(desc).hasArgs().required().type(ArrayList.class)
                .argName("compile").build());

        // Testing mode
        desc = "Debug mode" +
                "\nUsage: -d";
        options.addOption(Option.builder("d").longOpt("debug")
                .desc(desc).type(Boolean.class).hasArg(false).required(false)
                .argName("debug").build());

        // Run SSI Algorithm
        desc = "Run the SSI Algorithm.\nUsage: -ssi";
        options.addOption(Option.builder("ssi").longOpt("ssi")
                .desc(desc).type(Boolean.class).hasArg().required(false)
                .argName("ssi").build());

        // Output file option
        desc = "Place output in which directory.  If -t is set, this must be set." +
                "\n Usage: -o /path/to/output/";
        options.addOption(Option.builder("o").longOpt("output")
                .desc(desc).type(String.class).hasArg().required(false)
                .argName("output").build());

        // What translators to use
        desc = "What translator to use.  If -o is set, this must be set." +
                "\n Usage: -translate {list of translators}" +
                "\n Available translators: " +
                "\n\t mfsim: translates cfg to mfsim machine code" +
                "\n\t typesystem: translates cfg for further typing analysis";
        options.addOption(Option.builder("t").longOpt("translate")
                .desc(desc).type(ArrayList.class).hasArgs().required(false)
                .argName("translate").build());

        // Clean output option
        desc = "Clean the output directory. If -clean is set, -o (output) must be set." +
                "\nUsage: -clean";
        options.addOption(Option.builder("clean").longOpt("clean")
                .desc(desc).type(Boolean.class).hasArg(false).required(false)
                .argName("clean").build());
        
        desc = "What phases to enable." +
                "\n Usage: -p {list of phases}" +
                "\n Available phases: " +
                "\n\t inference: run type inference";
        options.addOption(Option.builder("p").longOpt("phases")
            .desc(desc).hasArgs().required(false)
            .argName("phases").build());
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
        logger.info(t);
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
        logger.info(t);

        logger.info(pt);
    }

}
