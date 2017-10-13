package typesystem.epa;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @created: 9/7/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public enum ChemTypes {
    ACIDS_STRONG_NON_OXIDIZING(1),
    ACIDS_STRONG_OXIDIZING(2),
    ACIDS_CARBOXYLIC(3),
    ALCOHOLS_AND_POLYOLS(4),
    ALDEHYDES(5),
    AMIDES_AND_IMIDES(6),
    AMINES_PHOSPHINES_AND_PYRIDINES(7),
    AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS(8),
    CARBAMATES(9),
    BASES_STRONG(10),
    CYANIDES_INORGANIC(11),
    THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS(12),
    ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS(13),
    ETHERS(14),
    FLUORIDES_INORGANIC(15),
    HYDROCARBONS_AROMATIC(16),
    HALOGENATED_ORGANIC_COMPOUNDS(17),
    ISOCYANATES_AND_ISOTHIOCYANATES(18),
    KETONES(19),
    SULFIDES_ORGANIC(20),
    METALS_ALKALI_VERY_ACTIVE(21),
    METALS_ELEMENTAL_AND_POWDER_ACTIVE(22),
    METALS_LESS_REACTIVE(23),
    DIAZONIUM_SALTS(25),
    NITRILES(26),
    NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC(27),
    HYDROCARBONS_ALIPHATIC_UNSATURATED(28),
    HYDROCARBONS_ALIPHATIC_SATURATED(29),
    PEROXIDES_ORGANIC(30),
    PHENOLS_AND_CRESOLS(31),
    SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC(32),
    SULFIDES_INORGANIC(33),
    EPOXIDES(34),
    METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES(35),
    ANHYDRIDES(37),
    SALTS_ACIDIC(38),
    SALTS_BASIC(39),
    ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES(40),
    ORGANOMETALLICS(42),
    OXIDIZING_AGENTS_STRONG(44),
    REDUCING_AGENTS_STRONG(45),
    NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS(46),
    FLUORINATED_ORGANIC_COMPOUNDS(47),
    FLUORIDE_SALTS_SOLUBLE(48),
    OXIDIZING_AGENTS_WEAK(49),
    REDUCING_AGENTS_WEAK(50),
    NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES(51),
    CHLOROSILANES(55),
    SILOXANES(58),
    HALOGENATING_AGENTS(59),
    ACIDS_WEAK(60),
    BASES_WEAK(61),
    CARBONATE_SALTS(62),
    ALKYNES_WITH_ACETYLENIC_HYDROGEN(63),
    ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN(64),
    CONJUGATED_DIENES(65),
    ARYL_HALIDES(66),
    AMINES_AROMATIC(68),
    NITRATE_AND_NITRITE_COMPOUNDS_INORGANIC(69),
    ACETALS_KETALS_HEMIACETALS_AND_HEMIKETALS(70),
    ACRYLATES_AND_ACRYLIC_ACIDS(71),
    PHENOLIC_SALTS(72),
    QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS(73),
    SULFITE_AND_THIOSULFATE_SALTS(74),
    OXIMES(75),
    POLYMERIZABLE_COMPOUNDS(76),
    NOT_CHEMICALLY_REACTIVE(98),
    INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION(99),
    WATER_AND_AQUEOUS_SOLUTIONS(100),
    REAL(128),
    NAT(129),
    MAT(130),
    CONST(131),
    FALSE(-1);

    private static Map<Integer, ChemTypes> integerChemTypesMap = new HashMap<Integer, ChemTypes>() {{
        put(1, ACIDS_STRONG_NON_OXIDIZING);
        put(2, ACIDS_STRONG_OXIDIZING);
        put(3, ACIDS_CARBOXYLIC);
        put(4, ALCOHOLS_AND_POLYOLS);
        put(5, ALDEHYDES);
        put(6, AMIDES_AND_IMIDES);
        put(7, AMINES_PHOSPHINES_AND_PYRIDINES);
        put(8, AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS);
        put(9, CARBAMATES);
        put(10, BASES_STRONG);
        put(11, CYANIDES_INORGANIC);
        put(12, THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS);
        put(13, ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS);
        put(14, ETHERS);
        put(15, FLUORIDES_INORGANIC);
        put(16, HYDROCARBONS_AROMATIC);
        put(17, HALOGENATED_ORGANIC_COMPOUNDS);
        put(18, ISOCYANATES_AND_ISOTHIOCYANATES);
        put(19, KETONES);
        put(20, SULFIDES_ORGANIC);
        put(21, METALS_ALKALI_VERY_ACTIVE);
        put(22, METALS_ELEMENTAL_AND_POWDER_ACTIVE);
        put(23, METALS_LESS_REACTIVE);
        put(25, DIAZONIUM_SALTS);
        put(26, NITRILES);
        put(27, NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC);
        put(28, HYDROCARBONS_ALIPHATIC_UNSATURATED);
        put(29, HYDROCARBONS_ALIPHATIC_SATURATED);
        put(30, PEROXIDES_ORGANIC);
        put(31, PHENOLS_AND_CRESOLS);
        put(32, SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC);
        put(33, SULFIDES_INORGANIC);
        put(34, EPOXIDES);
        put(35, METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES);
        put(37, ANHYDRIDES);
        put(38, SALTS_ACIDIC);
        put(39, SALTS_BASIC);
        put(40, ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES);
        put(42, ORGANOMETALLICS);
        put(44, OXIDIZING_AGENTS_STRONG);
        put(45, REDUCING_AGENTS_STRONG);
        put(46, NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS);
        put(47, FLUORINATED_ORGANIC_COMPOUNDS);
        put(48, FLUORIDE_SALTS_SOLUBLE);
        put(49, OXIDIZING_AGENTS_WEAK);
        put(50, REDUCING_AGENTS_WEAK);
        put(51, NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES);
        put(55, CHLOROSILANES);
        put(58, SILOXANES);
        put(59, HALOGENATING_AGENTS);
        put(60, ACIDS_WEAK);
        put(61, BASES_WEAK);
        put(62, CARBONATE_SALTS);
        put(63, ALKYNES_WITH_ACETYLENIC_HYDROGEN);
        put(64, ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN);
        put(65, CONJUGATED_DIENES);
        put(66, ARYL_HALIDES);
        put(68, AMINES_AROMATIC);
        put(69, NITRATE_AND_NITRITE_COMPOUNDS_INORGANIC);
        put(70, ACETALS_KETALS_HEMIACETALS_AND_HEMIKETALS);
        put(71, ACRYLATES_AND_ACRYLIC_ACIDS);
        put(72, PHENOLIC_SALTS);
        put(73, QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS);
        put(74, SULFITE_AND_THIOSULFATE_SALTS);
        put(75, OXIMES);
        put(76, POLYMERIZABLE_COMPOUNDS);
        put(98, NOT_CHEMICALLY_REACTIVE);
        put(99, INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
        put(100, WATER_AND_AQUEOUS_SOLUTIONS);
        put(128, REAL);
        put(129, NAT);
        //put(130, MAT);
        //put(131, CONST);
    }};

    public static final int NUM_REACTIVE_GROUPS = integerChemTypesMap.size();

    public static Set<ChemTypes> getNums() {
        return new HashSet<ChemTypes>(){{
            add(REAL);
            add(NAT);
        }};
    }

    private int value;
    ChemTypes(int value) {
        this.value = value;
    }

    public int getValue() {
        return this.value;
    }

    public static ChemTypes getTypeFromId(int id) {
        if (integerChemTypesMap.get(id) == null) {
            return integerChemTypesMap.get(1);
        }
        return integerChemTypesMap.get(id);
    }

    public static Map<Integer, ChemTypes> getIntegerChemTypesMap() {
        return integerChemTypesMap;
    }

    public static boolean isNumber(ChemTypes t) {
        return (t == NAT || t == REAL);
    }

    public String toString(ChemTypes t) {
        return String.format("%s (%d)", t, t.value);
    }
}
