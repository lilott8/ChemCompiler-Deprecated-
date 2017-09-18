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
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

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
    // actual table that holds the results.
    static final Table<Integer, Integer, Set<Integer>> comboTable = HashBasedTable.create();
    // Cache for combining compounds.
    static final Table<Long, Long, ChemAxonCompound> comboCache = HashBasedTable.create();
    // Cache the creation of the chemicals.
    Map<Long, ChemAxonCompound> chemicalCache = new ConcurrentHashMap<>();
    AtomicInteger numChems = new AtomicInteger(0);

    Combiner combiner = CombinerFactory.getCombiner();
    Classifier classifier = ClassifierFactory.getClassifier();

    public ReactiveCombinator(ThreadedFile threadedFile) {
        super(threadedFile);
    }

    public void run() {
        ChemAxonCompound compound;
        int record;
        logger.info("Starting thread: ");
        while (!this.queue.isEmpty()) {
            record = this.queue.poll();
            logger.info("Running combos with rg: " + record);
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
                        compoundX = this.checkCache(compoundX, chemX);
                        // iterate as our "Y"
                        for (Chemical chemY : set2) {
                            // we don't need to compare the same
                            if (chemX.equals(chemY)) {
                                continue;
                            }
                            ChemAxonCompound compoundY = new ChemAxonCompound(chemY.pubChemId, chemY.canonicalSmiles);
                            compoundY = this.checkCache(compoundY, chemY);
                            compound = this.combineChems(compoundX, compoundY);
                            // Add the types to the map
                            // StringBuilder reactiveGroups = new StringBuilder();
                            Set<ChemTypes> types = this.classifyChem(compound);
                            this.addToTable(chemX, chemY, types);
                            // we write the table, so we don't need this.
                            /*
                            for (ChemTypes type : types) {
                                reactiveGroups.append(typet.getValue()).append("_");
                                addToTable(chemX, chemY, type.getValue());
                            }
                            this.writer.push(String.format("%s|%s|%s", chemX.reactiveGroup, chemY.reactiveGroup, reactiveGroups.toString()));
                            */
                        }
                    }
                } else {
                    this.addToTable(record, inner.getKey(), record);
                    this.addToTable(record, inner.getKey(), inner.getKey());
                }
            }
            if (this.queue.size() % 4 == 0) {
                logger.info(String.format("Done processing: %.4f%% of records.",
                        ((1-(this.queue.size() / (double) this.totalRecords)) * 100)));
                this.writeToDisk();
            }
        }
    }

    /**
     * Do the minimal work necessary to get this working.
     * Cache the result of chemicals so we don't have to continue to recalculate the expensive JCHEM calls.
     * @param compound
     * @param chem
     * @return
     */
    private ChemAxonCompound checkCache(ChemAxonCompound compound, Chemical chem) {
        if (chemicalCache.containsKey(compound.getId()) && chemicalCache.get(compound.getId()).getRepresentation() != null) {
            compound = chemicalCache.get(compound.getId());
        } else {
            compound = this.addMolecule(compound, chem);
            chemicalCache.put(compound.getId(), compound);
            numChems.getAndIncrement();
            if (numChems.get() % 100 == 0) {
                logger.debug(String.format("Done adding: %d\t (%.4f%% of records.)", numChems.get(), ((numChems.get()/(double) this.totalRecords)*100)));
            }
        }
        return compound;
    }

    private synchronized boolean inTable(int x, int y, int type) {
        if (x > y) {
            int temp = x;
            x = y;
            y = temp;
        }

        if (!comboTable.contains(x, y)) {
            comboTable.put(x, y, new HashSet<>());
            comboTable.get(x, y).add(y);
            return false;
        }

        if (!comboTable.get(x, y).contains(type)) {
            comboTable.get(x, y).add(type);
            return false;
        } else {
            return true;
        }
    }

    private synchronized ChemAxonCompound addMolecule(ChemAxonCompound a, Chemical chem) {
        try {
            a.setRepresentation(MolImporter.importMol(chem.canonicalSmiles));
        } catch(MolFormatException e) {
            logger.error("Could not instantiate: " + chem.pubChemId);
        }
        return a;
    }

    private synchronized boolean addToTable(int x, int y, int type) {
        // If we do one way dominated, we guarantee a sparse matrix.
        if (x > y) {
            int temp = x;
            x = y;
            y = temp;
        }
        if (!comboTable.contains(x, y)) {
            comboTable.put(x, y, new HashSet<>());
        }
        comboTable.get(x, y).add(type);
        // just to be sure, add the rgs of the current chemicals.
        comboTable.get(x, y).add(x);
        comboTable.get(x, y).add(y);
        return true;
    }

    private synchronized boolean addToTable(Chemical x, Chemical y, int type) {
        return this.addToTable(x.reactiveGroup, y.reactiveGroup, type);
    }

    private boolean addToTable(Chemical x, Chemical y, Set<ChemTypes> types) {
        for (ChemTypes t : types) {
            addToTable(x.reactiveGroup, y.reactiveGroup, t.getValue());
        }
        return true;
    }

    private synchronized ChemAxonCompound combineChems(ChemAxonCompound a, ChemAxonCompound b) {
        if (a.getId() > b.getId()) {
            ChemAxonCompound temp = a;
            b = a;
            a = temp;
        }

        if (comboCache.contains(a.getId(), b.getId())) {
            return comboCache.get(a.getId(), b.getId());
        } else {
            try {
                comboCache.put(a.getId(), b.getId(), (ChemAxonCompound) combiner.combine(a, b));
                return comboCache.get(a.getId(), b.getId());
            } catch (Exception e) {
                comboCache.put(a.getId(), b.getId(), (ChemAxonCompound) combiner.combine(a, b));
                return comboCache.get(a.getId(), b.getId());
            }
        }
    }

    private synchronized Set<ChemTypes> classifyChem(ChemAxonCompound compound) {
        return classifier.classify(compound);
    }

    public synchronized void writeToDisk() {
        for (Table.Cell<Integer, Integer, Set<Integer>> cell: comboTable.cellSet()){
            StringBuilder sb = new StringBuilder();
            sb.append(cell.getRowKey()).append("|").append(cell.getColumnKey()).append("|");
            for (int type : cell.getValue()) {
                sb.append(type).append("_");
            }
            this.writer.push(sb.toString());
            //System.out.println(cell.getRowKey()+" "+cell.getColumnKey()+" "+cell.getValue());
        }
    }
}
