import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.concurrent.TimeUnit;

import cli.CliWrapper;
import config.ConfigFactory;
import reactivetable.ChemicalCombinator;
import reactivetable.TableCombinator;
import reactivetable.ThreadManager;
import shared.io.file.write.FileWriter;
import shared.io.file.write.SimpleWriter;

/**
 * @created: 9/14/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TableMain {

    public static final Logger logger = LogManager.getLogger(TableMain.class);

    public static void main(String... args) {
        CliWrapper cli = new CliWrapper();
        cli.parseCommandLine(args);

        //EpaManager.INSTANCE.buildEPAMap();

        ThreadManager threadManager = new ThreadManager();
        // Instantiate the threaded file manager.
        FileWriter fileManager = new SimpleWriter("elisa", true);

        // Create the new combinator
        TableCombinator combo = new ChemicalCombinator(fileManager);
        // TableCombinator combo = new StatisticCombinator(fileManager);

        // run the file manager as a new thread.
        // fileManager.start();
        // threadManager.runThread(new Thread(fileManager, String.format("Thread-%d", threadManager.getNextInstructionId())));
        // Add the correct number of combine threads.
        for (int x = 0; x < ConfigFactory.getConfig().getNumberOfThreads(); x++) {
            //for (int x = 0; x < 1; x++) {
            threadManager.addThread(new Thread(combo, String.format("Thread-%d", threadManager.getNextId())));
        }

        // Run the thread pool!
        threadManager.runExecutor();

        long start = System.currentTimeMillis();
        // block anything else from happening!
        while (!threadManager.isDone()) {
        }
        // write the table to disk.
        //combo.writeToDisk();

        // Notify the fileManager that we are done working.
        fileManager.sendDoneSignal();
        logger.info(getRealTime("Total execution time", (System.currentTimeMillis() - start)));
    }

    public static String getRealTime(String string, long time) {
        return String.format("%s: %02d:%02d:%02d", string,
                TimeUnit.MILLISECONDS.toHours(time),
                TimeUnit.MILLISECONDS.toMinutes(time % TimeUnit.HOURS.toMinutes(1)),
                TimeUnit.MILLISECONDS.toSeconds(time) % TimeUnit.MINUTES.toSeconds(1));
    }


}
