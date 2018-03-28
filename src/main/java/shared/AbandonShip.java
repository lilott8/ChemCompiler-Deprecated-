package shared;

import org.apache.logging.log4j.LogManager;

/**
 * @created: 3/27/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public final class AbandonShip {

    public static void abandonShip(String message, String callee) {
        LogManager.getLogger(AbandonShip.class).fatal(String.format("Abandoning ship from: %s \t " +
                "with message: %s\t%s", callee, System.lineSeparator(), message));
    }
}
