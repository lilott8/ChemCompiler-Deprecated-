package config;

import org.apache.commons.cli.CommandLine;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.Map;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public final class ConfigFactory {

    public static final Logger logger = LogManager.getLogger(ConfigFactory.class);
    public static final String configName = "default";

    private static Map<String, Config> configCache = new HashMap<>();

    public static Config buildConfig(CommandLine cmd) {
        return ConfigFactory.buildConfig(cmd, configName);
    }

    public static Config buildConfig(CommandLine cmd, String name) {
        if (!configCache.containsKey(name)) {
            Config config = new Config(cmd);
            configCache.put(name, config);
        }
        return configCache.get(name);
    }

    public static Config getConfig(String name) {
        if (configCache.containsKey(name)) {
            return configCache.get(name);
        }
        logger.warn("No config exists for: " + name);
        return null;
    }

    public static Config getConfig() {
        return getConfig(configName);
    }
}
