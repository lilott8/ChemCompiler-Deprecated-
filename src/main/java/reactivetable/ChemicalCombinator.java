package reactivetable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import io.file.FileHandler;
import shared.substances.ChemAxonCompound;
import typesystem.epa.ChemTypes;

/**
 * @created: 10/2/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ChemicalCombinator extends TableCombinator {

    // List of IDs for the chemicals
    List<Long> chemicalIds = new ArrayList<>();


    public ChemicalCombinator(FileHandler handler) {
        super(handler);
        chemicalIds.addAll(this.chemicalCache.keySet());
    }

    @Override
    public void run() {
        // Wrap it in the try/catch just to be sure.
        try {
            int counter = 0;
            int total = this.chemicalIds.size() * this.chemicalIds.size();
            for (long x : this.chemicalIds) {
                for (long y : this.chemicalIds) {
                    if (x != y) {
                        ChemAxonCompound compound = this.combineChems(this.chemicalCache.get(x), this.chemicalCache.get(y));
                        Set<ChemTypes> result = this.classifyChem(compound);
                        this.addReactiveGroups(this.chemicalCache.get(x), this.chemicalCache.get(y), result);
                    } else {
                        this.addReactiveGroups(this.chemicalCache.get(x), this.chemicalCache.get(y), this.chemicalCache.get(x).getReactiveGroups());
                    }
                    counter++;

                    if (counter % 1000 == 0) {
                        this.logProgress(counter, total);
                    }
                }
                // Write the table to disk.
                this.writer.writeTable(this.comboTable);
                // This saves the table in an iterative form,
                // There will be queue.size() files, monotonic in nature.
                this.writer.changeFile();
                // Save our completed list.
                this.doneWriter.write(x);
                // Save the record to file.
                this.doneWriter.flush();
                // Give a quick status update.
                this.logProgress(counter, total);
            }
            // Close the done file!
            this.doneWriter.sendDoneSignal();
        } catch (Exception e) {
            logger.error(e);
            this.writer.writeTable(this.comboTable);
            this.writer.sendDoneSignal();
            this.doneWriter.sendDoneSignal();
        }
    }

    private void logProgress(int counter, int total) {
        double percent = (counter / (double) total) * 100;
        logger.info(String.format("Done processing: %.4f%% of records.", percent));
    }

    private void addReactiveGroups(ChemAxonCompound x, ChemAxonCompound y, Set<ChemTypes> result) {
        for (ChemTypes rg1 : x.getReactiveGroups()) {
            for (ChemTypes rg2 : y.getReactiveGroups()) {
                for (ChemTypes res : result) {
                    this.addToTable(rg1.getValue(), rg2.getValue(), res.getValue());
                }
            }
        }
    }

    @Override
    public void printReactiveGroupTable() {
        logger.info("We have: " + this.chemicalCache.keySet().size() + " chemicals to work through.");
    }
}
