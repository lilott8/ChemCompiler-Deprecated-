package simulator;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import config.ConfigFactory;
import config.DatabaseConfig;
import phases.inference.ChemTypes;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class FauxIdentifier implements Identify {

    public static final Logger logger = LogManager.getLogger(FauxIdentifier.class);

    // Handles what the outcome of mixing several elements together is.
    private Table<Integer, Integer, Set<ChemTypes>> comboTable = HashBasedTable.create();
    // Just for convenience, not really necessary.
    private Map<Integer, ChemTypes> reactiveGroups = new HashMap<>();
    // Used to get a random value for selection
    private List<Integer> reactiveGroupIds = new ArrayList<>();

    public FauxIdentifier() {
        DatabaseConfig config = ConfigFactory.getConfig();
        loadTable();
        loadReactiveGroups();
    }

    @Override
    public Set<ChemTypes> getReactiveGroup(String name) {
        Random random = new Random();
        Set<ChemTypes> types = new HashSet<>();
        int numRGs = random.nextInt(3 - 1) + 1;
        for (int x = 0; x < numRGs; x++) {
            int t = random.nextInt(this.reactiveGroupIds.size());
            // We can't have 99, right now.
            while (t == 99) {
                t = random.nextInt(this.reactiveGroupIds.size());
            }
            types.add(this.reactiveGroups.get(this.reactiveGroupIds.get(t)));
        }
        return types;
    }

    @Override
    public Set<ChemTypes> getReaction(int rg1, int rg2) {
        if (this.comboTable.get(rg1, rg2) == null) {
            //logger.error(rg1 + ", " + rg2 + " yielded a null value");
            return new HashSet<>();
        }
        return this.comboTable.get(rg1, rg2);
    }

    @Override
    public Set<ChemTypes> getReaction(ChemTypes rg1, ChemTypes rg2) {
        return this.getReaction(rg1.getValue(), rg2.getValue());
    }

    private void loadTable() {
        try {
            BufferedReader reader = new BufferedReader(new InputStreamReader(new FileInputStream("src/main/resources/rg_combos.txt")));

            String line;
            while ((line = reader.readLine()) != null) {
                String[] array = StringUtils.split(line, "|");
                int row = Integer.parseInt(array[1]);
                int column = Integer.parseInt(array[2]);
                if (!this.comboTable.contains(row, column)) {
                    this.comboTable.put(row, column, new HashSet<>());
                }
                this.comboTable.get(row, column).add(ChemTypes.getTypeFromId(Integer.parseInt(array[3])));
            }
            reader.close();
        } catch(Exception e) {
            logger.error("Could not load file.");
            logger.error(e);
        }
    }

    private void loadReactiveGroups() {
        try {
            BufferedReader reader = new BufferedReader(new InputStreamReader(new FileInputStream("src/main/resources/reactive_groups.txt")));

            String line;
            while ((line = reader.readLine()) != null) {
                String[] array = StringUtils.split(line, "|");
                this.reactiveGroups.put(Integer.parseInt(array[2]), ChemTypes.getTypeFromId(Integer.parseInt(array[2])));
                this.reactiveGroupIds.add(Integer.parseInt(array[2]));
            }
            reader.close();
        } catch(Exception e) {
            logger.error("Could not load file.");
            logger.error(e);
        }
    }
}
