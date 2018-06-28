package shared;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @created: 6/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public enum Statistics {
    INSTANCE;

    public static final String INFERENCE = "INFERENCE";
    public static final String TYPE_CHECKING = "TYPE CHECKING";
    public static final String PARSING = "PARSING";
    public static final String COMPILATION = "COMPILATION";
    private Map<String, List<String>> stats = new HashMap<>();
    private String NL = System.lineSeparator();

    public void addStatsCategory(String title) {
        if (!this.stats.containsKey(title)) {
            this.stats.put(title, new ArrayList<>());
        }
    }

    public void addRecord(String title, String record) {
        this.addStatsCategory(title);
        this.stats.get(title).add(record);
    }

    public Map<String, List<String>> getStats() {
        return stats;
    }

    public String printStats() {
        StringBuilder sb = new StringBuilder(NL);

        for (Map.Entry<String, List<String>> entry : stats.entrySet()) {
            sb.append("===== ").append(entry.getKey()).append(" =====").append(NL);
            for (String record : entry.getValue()) {
                sb.append(record).append(NL);
            }
            sb.append("===== END ").append(entry.getKey()).append(" =====").append(NL);
        }

        return sb.toString();
    }
}
