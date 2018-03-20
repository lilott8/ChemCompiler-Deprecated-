package reactivetable;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import chemaxon.formats.MolFormatException;
import chemaxon.formats.MolImporter;
import chemical.classification.Classifier;
import chemical.classification.ClassifierFactory;
import chemical.combinator.Combiner;
import chemical.combinator.CombinerFactory;
import chemical.epa.ChemTypes;
import config.ConfigFactory;
import config.InferenceConfig;
import shared.io.file.write.FileWriter;
import shared.io.file.write.SimpleWriter;
import shared.substances.ChemAxonCompound;

/**
 * @created: 10/2/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class TableCombinator implements Runnable {
    protected static final Logger logger = LogManager.getLogger(TableCombinator.class);
    // file to write things to disk
    protected final FileWriter writer;
    protected final FileWriter doneWriter;
    // Cache for combining compounds.
    protected final Table<Long, Long, ChemAxonCompound> comboCache = HashBasedTable.create();
    // Actual table that holds the results.
    // X,y coordinates retrieve the resultant reactive groups of
    // Mixing the two groups together.
    protected final Table<Integer, Integer, Set<Integer>> comboTable = HashBasedTable.create();
    // handy globals to make things easier.
    protected Combiner combiner = CombinerFactory.getCombiner();
    protected Classifier classifier = ClassifierFactory.getClassifier();
    // config for setting things
    protected InferenceConfig config = ConfigFactory.getConfig();
    // total records to be processed (queue.size() before runn())
    protected int totalRecords;
    // this houses all the reactive groups and their corresponding chemicals.
    protected Map<Integer, Set<ChemAxonCompound>> reactiveGroupToChemicals = new HashMap<>();
    // List of idCounter's we a
    protected Set<Integer> reactiveGroupId = new LinkedHashSet<>();
    // Cache the creation of the chemicals.
    protected Map<Long, ChemAxonCompound> chemicalCache = new HashMap<>();

    public TableCombinator(FileWriter handler) {
        this.writer = handler;
        this.buildChemicals(this.parseFile());
        this.doneWriter = new SimpleWriter("completed.txt", false);
    }

    public abstract void printReactiveGroupTable();

    /**
     * This parses the chemicals to a temporary container.
     * This temporary container just makes it easier to manage
     * The data and not have to put ugliness in here.
     *
     * @return List of chemicals.
     */
    private List<Chemical> parseFile() {
        BufferedReader reader = null;
        List<Chemical> results = new ArrayList<>();
        logger.info("Beginning parsing file.");
        try {
            File file = new File(this.config.getFilesForCompilation().get(0));
            reader = new BufferedReader(new FileReader(file));

            String line;
            while ((line = reader.readLine()) != null) {
                // Number of chemicals that ultimately need to be mixed.
                this.totalRecords++;
                Chemical chem = new Chemical(line);
                results.add(chem);
                this.reactiveGroupId.add(chem.reactiveGroup);
                // Make sure the reactiveGroupToChemicals has the sets they need!
                if (!this.reactiveGroupToChemicals.containsKey(chem.reactiveGroup)) {
                    this.reactiveGroupToChemicals.put(chem.reactiveGroup, new HashSet<>());
                }
            }
        } catch (IOException e) {
        } finally {
            if (reader != null) {
                try {
                    reader.close();
                } catch (IOException ee) {
                }
            }
        }
        logger.info("Done parsing file.");
        return results;
    }

    /**
     * Use ChemAxon to instantiate the chemicals.
     * Store those in the cache.  "Rip the band-aid off first."
     */
    protected void buildChemicals(List<Chemical> input) {
        int count = 0;

        logger.info("Beginning building chemicals.");
        for (Chemical chem : input) {
            //logger.info("On chemical: " + count + " (idCounter: " + chem.pubChemId + ")");
            // If we have seen the chemical before, add to the reactive group
            if (chemicalCache.containsKey(chem.pubChemId)) {
                chemicalCache.get(chem.pubChemId).addReactiveGroup(chem.reactiveGroup);
            } else {
                ChemAxonCompound compound = new ChemAxonCompound(chem.pubChemId, chem.canonicalSmiles);
                compound.setSmiles(chem.canonicalSmiles);
                compound.addReactiveGroup(chem.reactiveGroup);
                compound = this.addMolecule(compound, chem);
                chemicalCache.put(compound.getId(), compound);
            }
            count++;
            double done = 100 * (count / (double) input.size());
            if (input.size() % 100 == 0) {
                logger.debug(String.format("Done processing: %.4f%% chemicals", done));
            }
        }
        logger.info("Done building chemicals.");
        logger.info("Beginning adding chemicals to the reactive group table.");
        // this guarantees we have the correct information in the table.
        for (Map.Entry<Long, ChemAxonCompound> entry : chemicalCache.entrySet()) {
            this.addChemicalToReactiveGroups(entry.getValue());
        }
        logger.info("Done adding chemicals to reactive group table.");
        //printReactiveGroupTable();
    }

    /**
     * Adds the instantiated chemicals to their
     * Respective reactive group.
     *
     * @param compound ChemAxonCompound
     */
    private void addChemicalToReactiveGroups(ChemAxonCompound compound) {
        for (ChemTypes type : compound.getReactiveGroups()) {
            this.reactiveGroupToChemicals.get(type.getValue()).add(compound);
        }
    }

    /**
     * Wrapper funciton to add the molecule to the ChemAxonCompound
     *
     * @param a    ChemAxonCompound
     * @param chem Chemical object
     *
     * @return ChemAxonCompound with molecule.
     */
    private synchronized ChemAxonCompound addMolecule(ChemAxonCompound a, Chemical chem) {
        try {
            a.setRepresentation(MolImporter.importMol(chem.canonicalSmiles, "smiles"));
        } catch (MolFormatException e) {
            logger.error("Could not instantiate: " + chem.pubChemId);
        }
        return a;
    }

    /**
     * "Public" exposing method to add a reaction to the table
     *
     * @param chemX ChemAxonCompound
     * @param chemY ChemAxonCompound
     * @param types set of ChemTypes
     *
     * @return boolean
     */
    protected synchronized boolean addToTable(ChemAxonCompound chemX, ChemAxonCompound chemY, Set<ChemTypes> types) {
        for (ChemTypes x : chemX.getReactiveGroups()) {
            for (ChemTypes y : chemY.getReactiveGroups()) {
                for (ChemTypes type : types) {
                    this.addToTable(x.getValue(), y.getValue(), type.getValue());
                }
            }
        }
        return true;
    }

    /**
     * Ensures we always have a place to add the type to.
     * Sort by x ascending.
     *
     * @param x    int
     * @param y    int
     * @param type int
     *
     * @return boolean
     */
    protected synchronized boolean addToTable(int x, int y, int type) {
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

    /**
     * Combine the chemicals to get the resultant reactive group(s).
     * Order by x ascending.
     * This also classifies the compound.
     *
     * @param a ChemAxonCompound
     * @param b ChemAxonCompound
     *
     * @return ChemAxonCompound
     */
    protected synchronized ChemAxonCompound combineChems(ChemAxonCompound a, ChemAxonCompound b) {
        if (a.getId() > b.getId()) {
            ChemAxonCompound temp = a;
            b = a;
            a = temp;
        }

        if (this.comboCache.contains(a.getId(), b.getId())) {
            return this.comboCache.get(a.getId(), b.getId());
        } else {
            try {
                ChemAxonCompound compound = (ChemAxonCompound) combiner.combine(a, b);
                compound.addReactiveGroup(classifier.classify(compound));
                this.comboCache.put(a.getId(), b.getId(), compound);
                return this.comboCache.get(a.getId(), b.getId());
            } catch (Exception e) {
                ChemAxonCompound compound = new ChemAxonCompound(-1, "");
                compound.addReactiveGroup(a.getReactiveGroups());
                compound.addReactiveGroup(b.getReactiveGroups());
                this.comboCache.put(a.getId(), b.getId(), compound);
                return this.comboCache.get(a.getId(), b.getId());
            }
        }
    }

}
