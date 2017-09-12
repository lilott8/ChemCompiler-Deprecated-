import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * @created: 9/6/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ComboMain {

    public static Random random = new Random();
    public static int record = 1;

    public static List<Integer> reactiveGroups = new ArrayList<Integer>() {{
        add(1);
        add(2);
        add(3);
        add(4);
        add(5);
        add(6);
        add(7);
        add(8);
        add(9);
        add(10);
        add(11);
        add(12);
        add(13);
        add(14);
        add(16);
        add(17);
        add(18);
        add(19);
        add(20);
        add(21);
        add(22);
        add(23);
        add(25);
        add(26);
        add(27);
        add(28);
        add(29);
        add(30);
        add(31);
        add(32);
        add(33);
        add(34);
        add(35);
        add(37);
        add(38);
        add(39);
        add(40);
        add(42);
        add(44);
        add(45);
        add(46);
        add(47);
        add(48);
        add(49);
        add(50);
        add(51);
        add(55);
        add(58);
        add(59);
        add(60);
        add(61);
        add(62);
        add(63);
        add(64);
        add(65);
        add(66);
        add(68);
        add(69);
        add(70);
        add(71);
        add(72);
        add(73);
        add(74);
        add(75);
        add(76);
        add(98);
        add(99);
        add(100);
    }};

    public static void main(String... args) {
        int maxChemicals = 40;
        int minChemicals = 1;
        int maxReactions = 4;
        int minReactions = 1;

        for (int x = 0; x < reactiveGroups.size(); x++) {
            for (int y = x; y < reactiveGroups.size(); y++) {
                // simulate reactions.
                Set<Integer> reactions = new HashSet<>();
                reactions.add(reactiveGroups.get(x));
                reactions.add(reactiveGroups.get(y));
                if (x != y) {
                    int numReactions = random.nextInt(maxReactions - minReactions + 1) + minReactions;
                    for (int z = 0; z < numReactions; z++) {
                        reactions.add(reactiveGroups.get(random.nextInt(reactiveGroups.size() - 1) + 1));
                    }
                }
                writeToDisk(reactiveGroups.get(x), reactiveGroups.get(y), reactions);
            }
        }
    }

    public static void writeToDisk(int rg1, int rg2, Set<Integer> reactions) {
        StringBuilder sb = new StringBuilder();
        for(Integer x : reactions) {
            sb.append(record++).append("|").append(rg1).append("|").append(rg2).append("|").append(x).append(System.lineSeparator());
        }
        System.out.print(sb.toString());
    }

}
