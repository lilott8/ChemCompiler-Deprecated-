package compilation.symboltable;

import java.util.HashSet;
import java.util.Set;

import config.ConfigFactory;
import errors.UsageException;

/**
 * @created: 10/19/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class UsageGovernor {

    private static Set<String> aliveVariables = new HashSet<>();
    private static Set<String> killedVariables = new HashSet<>();

    public static void defVar(String name) {
        aliveVariables.add(name);
    }

    public static void useVar(String name) {
        if (killedVariables.contains(name)) {
            if (ConfigFactory.getConfig().monitorResources()) {
                throw new UsageException(name + " has already been consumed.  It cannot be used again.");
            }
        } else {
            aliveVariables.remove(name);
            killedVariables.add(name);
        }
    }
}
