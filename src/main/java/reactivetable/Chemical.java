package reactivetable;

import org.apache.commons.lang3.StringUtils;

/**
 * @created: 9/15/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Chemical {
    public final int reactiveGroup;
    public final long pubChemId;
    public final String name;
    public final String inchiKey;
    public final String inchi;
    public final String isomericSmiles;
    public final String canonicalSmiles;

    public Chemical(String line) {
        String[] temp = StringUtils.splitByWholeSeparatorPreserveAllTokens(line, "|_|");
        reactiveGroup = Integer.parseInt(temp[0]);
        pubChemId = Long.parseLong(temp[1]);
        name = temp[2];
        inchiKey = temp[3];
        inchi = temp[4];
        isomericSmiles = temp[5];
        canonicalSmiles = temp[6];
    }

    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (!Chemical.class.isAssignableFrom(obj.getClass())) {
            return false;
        }
        return this.pubChemId == ((Chemical) obj).pubChemId;
    }

    public String getKey() {
        return String.format("%d-%d", this.pubChemId, this.reactiveGroup);
    }
}
