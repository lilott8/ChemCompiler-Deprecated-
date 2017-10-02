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
        for (long x : this.chemicalIds) {
            for (long y : this.chemicalIds) {
                ChemAxonCompound compound = this.combineChems(this.chemicalCache.get(x), this.chemicalCache.get(y));
                Set<ChemTypes> result = this.classifyChem(compound);
                for (ChemTypes rg1 : this.chemicalCache.get(x).getReactiveGroups()) {
                    for (ChemTypes rg2 : this.chemicalCache.get(y).getReactiveGroups()) {
                        for (ChemTypes res : result) {
                            this.addToTable(rg1.getValue(), rg2.getValue(), res.getValue());
                        }
                    }
                }
            }
            // Write the table to disk.
            this.writer.writeTable(this.comboTable);
            // This saves the table in an iterative form,
            // There will be queue.size() files, monotonic in nature.
            this.writer.changeFile();
            // Save our completed list.
            this.doneWriter.write(x);
        }
        // Close the done file!
        this.doneWriter.sendDoneSignal();
    }

    @Override
    public void printReactiveGroupTable() {

    }
}
