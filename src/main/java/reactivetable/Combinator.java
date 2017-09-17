package reactivetable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.atomic.AtomicInteger;

import config.ConfigFactory;
import config.InferenceConfig;
import io.file.ThreadedFile;

/**
 * @created: 9/15/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */

abstract public class Combinator implements Runnable {
    public static Logger logger = LogManager.getLogger(Combinator.class);

    protected final Queue<Integer> queue = new ConcurrentLinkedQueue<>();

    protected final ThreadedFile writer;
    protected int totalRecords;
    InferenceConfig config = ConfigFactory.getConfig();
    protected Map<Integer, Set<Chemical>> reactiveGroupToChemicals = new LinkedHashMap<>();
    private Set<Integer> reactiveGroupId = new LinkedHashSet<>();

    protected volatile AtomicInteger currentRecord = new AtomicInteger(0);

    // Used for testing.
    public final static int modulo = 2;

    protected Combinator(ThreadedFile threadedFile) {
        this.writer = threadedFile;
        this.parseFile();

        this.queue.addAll(this.reactiveGroupId);

        logger.error("Size of queue: " + this.queue);
    }

    private void parseFile() {
        BufferedReader reader = null;

        try {
            File file = new File(this.config.getFilesForCompilation().get(0));
            reader = new BufferedReader(new FileReader(file));

            String line;
            while ((line = reader.readLine()) != null) {
                // Number of chemicals that ultimately need to be mixed.
                this.totalRecords++;
                Chemical chem = new Chemical(line);
                if (!this.reactiveGroupToChemicals.containsKey(chem.reactiveGroup)) {
                    this.reactiveGroupToChemicals.put(chem.reactiveGroup, new HashSet<>());
                }
                this.reactiveGroupToChemicals.get(chem.reactiveGroup).add(chem);
                this.reactiveGroupId.add(chem.reactiveGroup);
            }
        } catch (IOException e) {
        } finally {
            if (reader != null) {
                try {
                    reader.close();
                } catch(IOException ee) {}
            }
        }
    }

}
