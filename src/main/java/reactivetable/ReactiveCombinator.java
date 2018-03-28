package reactivetable;

import com.google.common.collect.Table;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;

import shared.io.file.write.FileWriter;
import shared.substances.ChemAxonCompound;

/**
 * @created: 9/14/17
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * This orders pair-wise comparison by reactive groups
 * e.g. every chemical in every reactive group will be combined.
 */
public class ReactiveCombinator extends TableCombinator {

    public static final Logger logger = LogManager.getLogger(ReactiveCombinator.class);

    // Queue of what needs to be processed (the reactive group ids)
    private final Queue<Integer> queue = new ConcurrentLinkedQueue<>();

    public ReactiveCombinator(FileWriter threadedFile) {
        super(threadedFile);
        this.queue.addAll(this.reactiveGroupId);
        logger.error("Size of queue: " + this.queue);
    }

    public void run() {
        ChemAxonCompound compound;
        int currentReactiveGroup;
        logger.info("Starting thread: ");
        while (!this.queue.isEmpty()) {
            currentReactiveGroup = this.queue.poll();
            logger.info("Running combos with rg: " + currentReactiveGroup);
            // Set of chemicals that belong to the group.
            Set<ChemAxonCompound> set1 = this.reactiveGroupToChemicals.get(currentReactiveGroup);
            // iterate the "inner" loop
            for (Map.Entry<Integer, Set<ChemAxonCompound>> inner : this.reactiveGroupToChemicals.entrySet()) {
                logger.debug(String.format("Beginning mixing RG: %d, %d", currentReactiveGroup, inner.getKey()));
                int loopCounter = 0;
                // We don't need to do diagonal comparisons (3,3) or (5,5)
                if (currentReactiveGroup != inner.getKey()) {
                    // Set of chemicals that belong to the group.
                    Set<ChemAxonCompound> set2 = inner.getValue();
                    // Iterate as our "X"
                    for (ChemAxonCompound chemX : set1) {
                        // iterate as our "Y"
                        for (ChemAxonCompound chemY : set2) {
                            // we don't need to compare the same
                            if (chemX.equals(chemY)) {
                                continue;
                            }
                            logger.trace(String.format("Beginning chemical simulation for: %d, %d (iter: %d)", currentReactiveGroup, inner.getKey(), loopCounter));
                            compound = this.combineChems(chemX, chemY);
                            // Add the types to the map
                            logger.trace(String.format("Done chemical simulation for: %d, %d (iter: %d)", currentReactiveGroup, inner.getKey(), loopCounter));
                            this.addToTable(chemX, chemY, compound.getReactiveGroups());
                            loopCounter++;
                        }
                    }
                } else {
                    this.addToTable(currentReactiveGroup, inner.getKey(), currentReactiveGroup);
                }
                logger.debug(String.format("Done mixing for RG: %d, %d", currentReactiveGroup, inner.getKey()));
            } // for each RG
            if (this.queue.size() % 4 == 0) {
                logger.info(String.format("Done processing: %.4f%% of records.",
                        ((1 - (this.queue.size() / (double) this.totalRecords)) * 100)));
            }
            // Write the table to disk.
            this.writer.writeTable(this.comboTable);
            // This saves the table in an iterative form,
            // There will be queue.size() files, monotonic in nature.
            this.writer.changeFile();
            // Save our completed list.
            this.doneWriter.write(currentReactiveGroup);
        }
        // Close the done file!
        this.doneWriter.sendDoneSignal();
    }


    /**
     * Write portions of the table to disk.
     * Useful for obtaining intermediate results.
     */
    public synchronized void writeToDisk() {
        for (Table.Cell<Integer, Integer, Set<Integer>> cell : comboTable.cellSet()) {
            StringBuilder sb = new StringBuilder();
            sb.append(cell.getRowKey()).append("|").append(cell.getColumnKey()).append("|");
            for (int type : cell.getValue()) {
                sb.append(type).append("_");
            }
            this.writer.push(sb.toString());
            //System.out.println(cell.getRowKey()+" "+cell.getColumnKey()+" "+cell.getValue());
        }
    }


    public void printReactiveGroupTable() {
        StringBuilder sb = new StringBuilder();
        int total = 0;
        int max = -1;
        int idOfMax = -1;
        for (Map.Entry<Integer, Set<ChemAxonCompound>> entry : this.reactiveGroupToChemicals.entrySet()) {
            sb.append("Reactive Group: ").append(entry.getKey()).append(System.lineSeparator());
            sb.append("Has ").append(entry.getValue().size()).append(" chemicals").append(System.lineSeparator());
            total += entry.getValue().size();
            for (ChemAxonCompound chem : entry.getValue()) {
                sb.append(chem.getId()).append(", ");
            }
            if (max < entry.getValue().size()) {
                max = entry.getValue().size();
                idOfMax = entry.getKey();
            }

            sb.append(System.lineSeparator());
            sb.append("=======================================").append(System.lineSeparator());
        }

        sb.append("Total chemicals: ").append(total).append(System.lineSeparator());
        sb.append(idOfMax).append(" has the most at: ").append(max);
        logger.warn(sb.toString());
    }
}
