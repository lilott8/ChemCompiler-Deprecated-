package Config;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;

import java.util.HashMap;
import java.util.Map;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public enum Config {
    INSTANCE;

    private Map<String, Setting> options = new HashMap<String, Setting>();
    private boolean built = false;

    public void buildConfig(CommandLine cmd) {
        if(!this.built) {
            for(Option option : cmd.getOptions()) {
                if (option.hasArg()) {
                    this.options.put(option.getArgName(), new Setting(option.getValue()));
                } else {
                    this.options.put(option.getArgName(), new Setting<Boolean>(true));
                }
            }
            this.built = true;
        }
    }

    public Setting get(String key) {
        if (this.options.containsKey(key)) {
            return this.options.get(key);
        }
        return null;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder(super.toString()).append(System.lineSeparator());

        for (Map.Entry<String, Setting> entity : this.options.entrySet()) {
            sb.append(entity.getKey()).append(":\t").append(entity.getValue()).append(System.lineSeparator());
        }
        return sb.toString();
    }
}
