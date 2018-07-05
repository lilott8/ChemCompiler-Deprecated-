package compilation.symboltable;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.Set;

import config.ConfigFactory;
import shared.errors.UsageException;
import symboltable.SymbolTable;

/**
 * @created: 10/19/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class UsageGovernor {

    public static final Logger logger = LogManager.getLogger(UsageGovernor.class);
    private static Set<String> aliveVariables = new HashSet<>();
    private static Set<String> killedVariables = new HashSet<>();
    private static Set<String> globalVariables = new HashSet<>();

    public static void reset() {
        aliveVariables.clear();
        killedVariables.clear();
        globalVariables.clear();
    }

    public static void defVar(String name) {
        if (SymbolTable.INSTANCE.getConstants().containsKey(name)) {
            globalVariables.add(name);
        } else {
            aliveVariables.add(name);
            if (killedVariables.contains(name)) {
                logger.warn(name + " has been used, assuming a new assignment.");
                killedVariables.remove(name);
            }
        }
    }

    public static void useVar(String name) {
        if (killedVariables.contains(name)) {
            if (ConfigFactory.getConfig().monitorResources()) {
                throw new UsageException(name + " has already been consumed.  It cannot be used again.");
            }
        } else {
            if (!globalVariables.contains(name)) {
                aliveVariables.remove(name);
                killedVariables.add(name);
            }
        }
    }
}
