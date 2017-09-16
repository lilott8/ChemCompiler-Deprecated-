package reactivetable;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import chemaxon.formats.MolFormatException;
import chemaxon.formats.MolImporter;
import config.ConfigFactory;
import config.InferenceConfig;
import io.file.ThreadedFile;
import shared.substances.ChemAxonCompound;
import typesystem.classification.Classifier;
import typesystem.classification.ClassifierFactory;
import typesystem.combinator.Combiner;
import typesystem.combinator.CombinerFactory;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/14/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ReactiveCombinator extends Combinator {

    public static final Logger logger = LogManager.getLogger(ReactiveCombinator.class);


    Table<Integer, Integer, Set<Integer>> comboTable = HashBasedTable.create();


    public ReactiveCombinator(ThreadedFile threadedFile) {
        super(threadedFile);
    }

    public void writeComboToDisk() throws Exception {
        BufferedWriter bw = null;
        File file = new File(this.config.getOutputDir());
        if (!file.exists()) {
            file.createNewFile();
        }
        FileWriter fw = new FileWriter(file);
        bw = new BufferedWriter(fw);

        StringBuilder sb = new StringBuilder();
        StringBuilder endProduct = new StringBuilder();

        Map<Integer, Map<Integer, Set<Integer>>> map = this.comboTable.rowMap();
        for(int x : map.keySet()) {
            String xValue = x + "|";
            Map<Integer, Set<Integer>> column = map.get(x);
            for (Map.Entry<Integer, Set<Integer>> entry : column.entrySet()) {
                String yValue = entry.getKey() + "|";
                for(int value : entry.getValue()) {
                    endProduct.append(value).append("_");
                }
                bw.write(xValue + yValue + endProduct.toString());
                bw.newLine();
                endProduct = new StringBuilder();
            }
            sb = new StringBuilder();
        }
        bw.close();
    }

    public void run() {
        Combiner combiner = CombinerFactory.getCombiner();
        Classifier classifier = ClassifierFactory.getClassifier();
        ChemAxonCompound compound;
        int record;
        logger.info("Starting thread: ");
        while (!this.queue.isEmpty()) {
            record = this.queue.poll();
            Set<Chemical> set1 = this.reactiveGroupToChemicals.get(record);
            // iterate the "inner" loop
            for (Map.Entry<Integer, Set<Chemical>> inner : this.reactiveGroupToChemicals.entrySet()) {
                if (inner.getKey() != record) {
                    int group2 = inner.getKey();
                    Set<Chemical> set2 = inner.getValue();

                    // Iterate as our "X"
                    for (Chemical chemX : set1) {
                        // Instantiate the compound
                        ChemAxonCompound compoundX = new ChemAxonCompound(chemX.pubChemId, chemX.canonicalSmiles);
                        compoundX = this.addMolecule(compoundX, chemX);
                        for (Chemical chemY : set2) {
                            // we don't need to compare the same
                            if (chemX.equals(chemY)) {
                                continue;
                            }
                            ChemAxonCompound compoundY = new ChemAxonCompound(chemY.pubChemId, chemY.canonicalSmiles);
                            compoundY = this.addMolecule(compoundY, chemY);
                            compound = (ChemAxonCompound) combiner.combine(compoundX, compoundY);
                            // Add the types to the map
                            StringBuilder reactiveGroups = new StringBuilder();
                            for (ChemTypes types : classifier.classify(compound)) {
                                reactiveGroups.append(types.getValue()).append("_");
                                addToTable(chemX, chemY, types.getValue());
                            }
                            // Save if we need to.
                            this.writer.push(String.format("%s|%s|%s", chemX.reactiveGroup, chemY.reactiveGroup, reactiveGroups.toString()));
                        }
                    }
                }
            }
            if (this.queue.size() % 4 == 0) {
                logger.info(String.format("Done processing: %.4f%% of records.",
                        (this.queue.size() / (double) this.totalRecords * 100)));
            }
        }
    }

    private void determineWrite(long x, long y, String string) {
        if (x > y) {
            this.writer.push(string);
        }
    }

    private ChemAxonCompound addMolecule(ChemAxonCompound a, Chemical chem) {
        try {
            a.setRepresentation(MolImporter.importMol(chem.canonicalSmiles));
        } catch(MolFormatException e) {
            logger.error("Could not instantiate: " + chem.pubChemId);
        }
        return a;
    }

    private boolean addToTable(Chemical x, Chemical y, int type) {
        // If we do one way dominated, we guarantee a sparse matrix.
        if (x.reactiveGroup < y.reactiveGroup) {
            Chemical temp = x;
            x = y;
            y = temp;
        }
        if (!this.comboTable.contains(x.reactiveGroup, y.reactiveGroup)) {
            this.comboTable.put(x.reactiveGroup, y.reactiveGroup, new HashSet<>());
        }
        this.comboTable.get(x.reactiveGroup, y.reactiveGroup).add(type);
        return true;
    }
}
