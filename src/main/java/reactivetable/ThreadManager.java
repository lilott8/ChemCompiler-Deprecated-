package reactivetable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

import config.ConfigFactory;
import config.InferenceConfig;

/**
 * @created: 9/15/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ThreadManager {

    public static final Logger logger = LogManager.getLogger(ThreadManager.class);
    private static final int MAXTHREADS = 100;
    private static int currentThreadId = 0;
    protected ConcurrentLinkedQueue<Thread> workers = new ConcurrentLinkedQueue<Thread>();
    private int numThreads;
    private ThreadPoolExecutor executor;
    private InferenceConfig config = ConfigFactory.getConfig();

    public ThreadManager() {
        numThreads = config.getNumberOfThreads();
        executor = new ThreadPoolExecutor(MAXTHREADS, MAXTHREADS, TimeUnit.SECONDS.toSeconds(10),
                TimeUnit.SECONDS, new ArrayBlockingQueue<>(MAXTHREADS));
    }

    public void addThread(Thread r) {
        this.workers.add(r);
    }

    public void runExecutor() {
        for (Thread t : workers) {
            executor.execute(t);
            logger.info("Executing thread: " + t.getId());
        }
        executor.shutdown();
    }

    public void runThread(Thread thread) {
        executor.execute(thread);
    }

    public int getNextId() {
        currentThreadId += 1;
        return currentThreadId - 1;
    }

    public int getNumThreadsExecuting() {
        return executor.getActiveCount();
    }

    public boolean isDone() {
        return this.executor.isTerminated();
    }
}

