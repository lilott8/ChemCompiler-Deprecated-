package reactivetable;

import org.apache.commons.lang3.StringUtils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import io.file.read.FileReader;
import io.file.read.SimpleReader;
import io.file.write.FileWriter;
import io.file.write.SimpleWriter;
import shared.substances.ChemAxonCompound;

/**
 * @created: 10/9/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * This builds a statistically significant representation
 * Of chemical mixes
 */
public class StatisticCombinator extends TableCombinator {

    private FileReader reader;
    public static final FileWriter writer = new SimpleWriter("stats.txt");
    private Map<Integer, Set<Long>> output = new HashMap<>();
    //private FileWriter writer;
    Map<Integer, Set<Long>> reactiveGroupsToDistinctChemicals = new HashMap<>();

    public StatisticCombinator(FileWriter handler) {
        super(handler);
        // TODO: change this to an ARG, not fixed.
        this.reader = new SimpleReader("path/to/list/of/distinct_chemicals.txt");
        this.parseFile();
        this.reader.close();

    }

    private void parseFile() {
        String line;
        while((line = this.reader.nextLine()) != null) {
            String[] array = StringUtils.split(line, "|_|");
            int x = Integer.parseInt(array[0]);
            long y = Long.parseLong(array[1]);
            if (!this.reactiveGroupsToDistinctChemicals.containsKey(x)) {
                this.reactiveGroupsToDistinctChemicals.put(x, new HashSet<>());
            }
            this.reactiveGroupsToDistinctChemicals.get(x).add(y);
        }
    }

    @Override
    public void printReactiveGroupTable() {
        StringBuilder sb = new StringBuilder(System.lineSeparator());
        String del = "|_|";
        Set<Integer> invalids = new HashSet<>();
        // Insufficient data
        invalids.add(99);
        // Not Chemically Reactive
        invalids.add(98);
        // Unknown?
        invalids.add(-1);
        for (Map.Entry<Integer, Set<Long>> entry : this.output.entrySet()) {
            if (!invalids.contains(entry.getKey())) {
                for (long id : entry.getValue()) {
                    ChemAxonCompound c = this.chemicalCache.get(id);
                    sb.append(entry.getKey()).append(del).append(c.getId()).append(del)
                            .append(c.getName()).append(del).append(del).append(del)
                            .append(c.getSmiles()).append(del)
                            .append(c.getSmiles()).append(System.lineSeparator());
                }
            }
        }

        logger.debug(sb);

        //logger.debug(this.output);
    }

    @Override
    public void run() {
        logger.info("Stats for chems");
        this.printStatsForRG2Chems();
        logger.info("Stats for distinct chems");
        this.printStatsForRG2DistinctChems();

        for (Map.Entry<Integer, Set<Long>> entry : this.reactiveGroupsToDistinctChemicals.entrySet()) {
            if (!this.output.containsKey(entry.getKey())) {
                this.output.put(entry.getKey(), new HashSet<>());
            }
            for (long x : entry.getValue()) {
                if (this.output.get(entry.getKey()).size() <= 10) {
                    this.output.get(entry.getKey()).add(x);
                }
            }
        }

        for (Map.Entry<Integer, Set<Long>> entry : this.output.entrySet()) {
            while (entry.getValue().size() < 10) {
                for (Map.Entry<Integer, Set<ChemAxonCompound>> rgc : this.reactiveGroupToChemicals.entrySet()) {
                    for (ChemAxonCompound cac : rgc.getValue()) {
                        if (entry.getValue().size() < 10) {
                            if (this.allowedToAdd(cac.getId())) {
                                entry.getValue().add(cac.getId());
                            }
                        } else {
                            break;
                        }
                    }
                }
            }
        }
        this.printReactiveGroupTable();
    }

    private boolean allowedToAdd(long id) {
        boolean result = true;
            for (Map.Entry<Integer, Set<Long>> entry : this.output.entrySet()) {
                if (entry.getValue().contains(id)) {
                    result = false;
                    break;
                }
        }

        return result;
    }

    private void printStatsForRG2DistinctChems() {
        int numChems = 0;
        int numGroups = 0;
        int max = 0;
        int maxReactiveGroup = 0;
        for(Map.Entry<Integer, Set<Long>> entry : this.reactiveGroupsToDistinctChemicals.entrySet()) {
            StringBuilder sb = new StringBuilder();
            sb.append(entry.getKey()).append(": ").append(entry.getValue().size());
            logger.info(sb);
            numChems += entry.getValue().size();
            numGroups++;
            if (entry.getValue().size() > max) {
                max = entry.getValue().size();
                maxReactiveGroup = entry.getKey();
            }
        }
        double percent = (numChems / (double) numGroups);
        logger.info(String.format("Each group has: %.4f records.", percent));
        logger.info(String.format("RG: %d has the max: %d", maxReactiveGroup, max));
    }

    private void printStatsForRG2Chems() {
        int numChems = 0;
        int numGroups = 0;
        int max = 0;
        int maxReactiveGroup = 0;
        for(Map.Entry<Integer, Set<ChemAxonCompound>> entry : this.reactiveGroupToChemicals.entrySet()) {
            StringBuilder sb = new StringBuilder();
            sb.append(entry.getKey()).append(": ").append(entry.getValue().size());
            logger.info(sb);
            numChems += entry.getValue().size();
            numGroups++;
            if (entry.getValue().size() > max) {
                max = entry.getValue().size();
                maxReactiveGroup = entry.getKey();
            }
        }
        double percent = (numChems / (double) numGroups);
        logger.info(String.format("Each group has: %.4f records.", percent));
        logger.info(String.format("RG: %d has the max: %d", maxReactiveGroup, max));
    }
}
