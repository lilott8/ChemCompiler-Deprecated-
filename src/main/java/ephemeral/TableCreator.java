package ephemeral;

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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import chemaxon.formats.MolFormatException;
import chemaxon.formats.MolImporter;
import config.CommonConfig;
import config.ConfigFactory;
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
public class TableCreator {

    public static final Logger logger = LogManager.getLogger(TableCreator.class);

    Table<Integer, Integer, Set<Integer>> naiveTable = HashBasedTable.create();
    Table<Integer, Integer, Set<Integer>> comboTable = HashBasedTable.create();
    CommonConfig config = ConfigFactory.getConfig();

    Map<Long, ChemAxonCompound> compoundCache = new HashMap<>();

    public void run() {
        this.parseFile();
        logger.info(naiveTable);
    }

    private void parseFile() {
        BufferedReader reader = null;

        try {
            File file = new File(this.config.getFilesForCompilation().get(0));
            reader = new BufferedReader(new FileReader(file));

            String line;
            List<Chemical> chems = new ArrayList<>();
            while ((line = reader.readLine()) != null) {
                chems.add(new Chemical(line));
            }
            this.buildComboTable(chems);
            try {
                this.writeComboToDisk();
            } catch(Exception e) {
                logger.error("Couldn't write to disk");
                logger.error(e);
            }
            //this.buildNaiveTable(chems);

        } catch (IOException e) {
            logger.error(e);
        } finally {
            try {
                reader.close();
            } catch (Exception e) {
                logger.error(e);
            }
        }
    }

    private void buildNaiveTable(List<Chemical> chems) {
        for(Chemical chemX : chems) {
            for(Chemical chemY : chems) {
                if(!this.naiveTable.contains(chemX.reactiveGroup, chemY.reactiveGroup)) {
                    this.naiveTable.put(chemX.reactiveGroup, chemY.reactiveGroup, new HashSet<>());
                }
                this.naiveTable.get(chemX.reactiveGroup, chemY.reactiveGroup).add(chemX.reactiveGroup);
                this.naiveTable.get(chemX.reactiveGroup, chemY.reactiveGroup).add(chemY.reactiveGroup);
            }
        }
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

    private void buildComboTable(List<Chemical> chems) {
        Combiner combiner = CombinerFactory.getCombiner();
        Classifier classifier = ClassifierFactory.getClassifier();
        ChemAxonCompound compound;
        long counter = 0;
        long totalCount = chems.size()*chems.size();
        if (config.isDebug()) {
            logger.trace("Running: " + totalCount + " iterations");
        }
        for(Chemical chemX : chems) {
            ChemAxonCompound compoundX = new ChemAxonCompound(chemX.pubChemId, chemX.canonicalSmiles);
            if (!compoundCache.containsKey(chemX.pubChemId)) {
                compoundX = addMolecule(compoundX, chemX);
                this.compoundCache.put(chemX.pubChemId, compoundX);
            } else {
                compoundX = this.compoundCache.get(chemX.pubChemId);
            }
            for(Chemical chemY : chems) {
                ChemAxonCompound compoundY = new ChemAxonCompound(chemY.pubChemId, chemY.canonicalSmiles);
                if(!this.compoundCache.containsKey(chemY.pubChemId)) {
                    compoundY = addMolecule(compoundY, chemY);
                    this.compoundCache.put(chemY.pubChemId, compoundY);
                } else {
                    compoundY = this.compoundCache.get(chemY.pubChemId);
                }
                compound = (ChemAxonCompound) combiner.combine(compoundX, compoundY);

                for(ChemTypes types : classifier.classify(compound)) {
                    if (!this.comboTable.contains(chemX.reactiveGroup,chemY.reactiveGroup)) {
                        this.comboTable.put(chemX.reactiveGroup, chemY.reactiveGroup, new HashSet<>());
                    }
                    this.comboTable.get(chemX.reactiveGroup, chemY.reactiveGroup).add(types.getValue());
                }
                if (this.config.isDebug()) {
                    if (counter % 100000 == 0) {
                        logger.debug(String.format("%.2f%% complete", 100 * (counter / (double) totalCount)));
                    }
                }
                counter++;
            }
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

    private class Chemical {
        public final int reactiveGroup;
        public final long pubChemId;
        public final String name;
        public final String inchiKey;
        public final String inchi;
        public final String isomericSmiles;
        public final String canonicalSmiles;

        public Chemical(String line) { ;
            String[] temp = StringUtils.splitByWholeSeparatorPreserveAllTokens(line, "|_|");
            reactiveGroup = Integer.parseInt(temp[0]);
            pubChemId = Long.parseLong(temp[1]);
            name = temp[2];
            inchiKey = temp[3];
            inchi = temp[4];
            isomericSmiles = temp[5];
            canonicalSmiles = temp[6];
        }
    }
}
