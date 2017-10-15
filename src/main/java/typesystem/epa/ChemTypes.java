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

    private static Map<Integer, ChemTypes> integerChemTypesMap = new HashMap<>();
    private static Set<ChemTypes> materials = new HashSet<>();
    private static Set<ChemTypes> numbers = new HashSet<>();

    static {
        integerChemTypesMap.put(1, ACIDS_STRONG_NON_OXIDIZING);
        integerChemTypesMap.put(2, ACIDS_STRONG_OXIDIZING);
        integerChemTypesMap.put(3, ACIDS_CARBOXYLIC);
        integerChemTypesMap.put(4, ALCOHOLS_AND_POLYOLS);
        integerChemTypesMap.put(5, ALDEHYDES);
        integerChemTypesMap.put(6, AMIDES_AND_IMIDES);
        integerChemTypesMap.put(7, AMINES_PHOSPHINES_AND_PYRIDINES);
        integerChemTypesMap.put(8, AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS);
        integerChemTypesMap.put(9, CARBAMATES);
        integerChemTypesMap.put(10, BASES_STRONG);
        integerChemTypesMap.put(11, CYANIDES_INORGANIC);
        integerChemTypesMap.put(12, THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS);
        integerChemTypesMap.put(13, ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS);
        integerChemTypesMap.put(14, ETHERS);
        integerChemTypesMap.put(15, FLUORIDES_INORGANIC);
        integerChemTypesMap.put(16, HYDROCARBONS_AROMATIC);
        integerChemTypesMap.put(17, HALOGENATED_ORGANIC_COMPOUNDS);
        integerChemTypesMap.put(18, ISOCYANATES_AND_ISOTHIOCYANATES);
        integerChemTypesMap.put(19, KETONES);
        integerChemTypesMap.put(20, SULFIDES_ORGANIC);
        integerChemTypesMap.put(21, METALS_ALKALI_VERY_ACTIVE);
        integerChemTypesMap.put(22, METALS_ELEMENTAL_AND_POWDER_ACTIVE);
        integerChemTypesMap.put(23, METALS_LESS_REACTIVE);
        integerChemTypesMap.put(25, DIAZONIUM_SALTS);
        integerChemTypesMap.put(26, NITRILES);
        integerChemTypesMap.put(27, NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC);
        integerChemTypesMap.put(28, HYDROCARBONS_ALIPHATIC_UNSATURATED);
        integerChemTypesMap.put(29, HYDROCARBONS_ALIPHATIC_SATURATED);
        integerChemTypesMap.put(30, PEROXIDES_ORGANIC);
        integerChemTypesMap.put(31, PHENOLS_AND_CRESOLS);
        integerChemTypesMap.put(32, SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC);
        integerChemTypesMap.put(33, SULFIDES_INORGANIC);
        integerChemTypesMap.put(34, EPOXIDES);
        integerChemTypesMap.put(35, METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES);
        integerChemTypesMap.put(37, ANHYDRIDES);
        integerChemTypesMap.put(38, SALTS_ACIDIC);
        integerChemTypesMap.put(39, SALTS_BASIC);
        integerChemTypesMap.put(40, ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES);
        integerChemTypesMap.put(42, ORGANOMETALLICS);
        integerChemTypesMap.put(44, OXIDIZING_AGENTS_STRONG);
        integerChemTypesMap.put(45, REDUCING_AGENTS_STRONG);
        integerChemTypesMap.put(46, NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS);
        integerChemTypesMap.put(47, FLUORINATED_ORGANIC_COMPOUNDS);
        integerChemTypesMap.put(48, FLUORIDE_SALTS_SOLUBLE);
        integerChemTypesMap.put(49, OXIDIZING_AGENTS_WEAK);
        integerChemTypesMap.put(50, REDUCING_AGENTS_WEAK);
        integerChemTypesMap.put(51, NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES);
        integerChemTypesMap.put(55, CHLOROSILANES);
        integerChemTypesMap.put(58, SILOXANES);
        integerChemTypesMap.put(59, HALOGENATING_AGENTS);
        integerChemTypesMap.put(60, ACIDS_WEAK);
        integerChemTypesMap.put(61, BASES_WEAK);
        integerChemTypesMap.put(62, CARBONATE_SALTS);
        integerChemTypesMap.put(63, ALKYNES_WITH_ACETYLENIC_HYDROGEN);
        integerChemTypesMap.put(64, ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN);
        integerChemTypesMap.put(65, CONJUGATED_DIENES);
        integerChemTypesMap.put(66, ARYL_HALIDES);
        integerChemTypesMap.put(68, AMINES_AROMATIC);
        integerChemTypesMap.put(69, NITRATE_AND_NITRITE_COMPOUNDS_INORGANIC);
        integerChemTypesMap.put(70, ACETALS_KETALS_HEMIACETALS_AND_HEMIKETALS);
        integerChemTypesMap.put(71, ACRYLATES_AND_ACRYLIC_ACIDS);
        integerChemTypesMap.put(72, PHENOLIC_SALTS);
        integerChemTypesMap.put(73, QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS);
        integerChemTypesMap.put(74, SULFITE_AND_THIOSULFATE_SALTS);
        integerChemTypesMap.put(75, OXIMES);
        integerChemTypesMap.put(76, POLYMERIZABLE_COMPOUNDS);
        integerChemTypesMap.put(98, NOT_CHEMICALLY_REACTIVE);
        integerChemTypesMap.put(99, INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
        integerChemTypesMap.put(100, WATER_AND_AQUEOUS_SOLUTIONS);
        integerChemTypesMap.put(128, REAL);
        integerChemTypesMap.put(129, NAT);
        //integerChemTypesMap.put(130, MAT);
        //integerChemTypesMap.put(131, CONST);

        numbers.add(REAL);
        numbers.add(NAT);

        materials.add(ACIDS_STRONG_NON_OXIDIZING);
        materials.add(ACIDS_STRONG_OXIDIZING);
        materials.add(ACIDS_CARBOXYLIC);
        materials.add(ALCOHOLS_AND_POLYOLS);
        materials.add(ALDEHYDES);
        materials.add(AMIDES_AND_IMIDES);
        materials.add(AMINES_PHOSPHINES_AND_PYRIDINES);
        materials.add(AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS);
        materials.add(CARBAMATES);
        materials.add(BASES_STRONG);
        materials.add(CYANIDES_INORGANIC);
        materials.add(THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS);
        materials.add(ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS);
        materials.add(ETHERS);
        materials.add(FLUORIDES_INORGANIC);
        materials.add(HYDROCARBONS_AROMATIC);
        materials.add(HALOGENATED_ORGANIC_COMPOUNDS);
        materials.add(ISOCYANATES_AND_ISOTHIOCYANATES);
        materials.add(KETONES);
        materials.add(SULFIDES_ORGANIC);
        materials.add(METALS_ALKALI_VERY_ACTIVE);
        materials.add(METALS_ELEMENTAL_AND_POWDER_ACTIVE);
        materials.add(METALS_LESS_REACTIVE);
        materials.add(DIAZONIUM_SALTS);
        materials.add(NITRILES);
        materials.add(NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC);
        materials.add(HYDROCARBONS_ALIPHATIC_UNSATURATED);
        materials.add(HYDROCARBONS_ALIPHATIC_SATURATED);
        materials.add(PEROXIDES_ORGANIC);
        materials.add(PHENOLS_AND_CRESOLS);
        materials.add(SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC);
        materials.add(SULFIDES_INORGANIC);
        materials.add(EPOXIDES);
        materials.add(METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES);
        materials.add(ANHYDRIDES);
        materials.add(SALTS_ACIDIC);
        materials.add(SALTS_BASIC);
        materials.add(ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES);
        materials.add(ORGANOMETALLICS);
        materials.add(OXIDIZING_AGENTS_STRONG);
        materials.add(REDUCING_AGENTS_STRONG);
        materials.add(NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS);
        materials.add(FLUORINATED_ORGANIC_COMPOUNDS);
        materials.add(FLUORIDE_SALTS_SOLUBLE);
        materials.add(OXIDIZING_AGENTS_WEAK);
        materials.add(REDUCING_AGENTS_WEAK);
        materials.add(NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES);
        materials.add(CHLOROSILANES);
        materials.add(SILOXANES);
        materials.add(HALOGENATING_AGENTS);
        materials.add(ACIDS_WEAK);
        materials.add(BASES_WEAK);
        materials.add(CARBONATE_SALTS);
        materials.add(ALKYNES_WITH_ACETYLENIC_HYDROGEN);
        materials.add(ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN);
        materials.add(CONJUGATED_DIENES);
        materials.add(ARYL_HALIDES);
        materials.add(AMINES_AROMATIC);
        materials.add(NITRATE_AND_NITRITE_COMPOUNDS_INORGANIC);
        materials.add(ACETALS_KETALS_HEMIACETALS_AND_HEMIKETALS);
        materials.add(ACRYLATES_AND_ACRYLIC_ACIDS);
        materials.add(PHENOLIC_SALTS);
        materials.add(QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS);
        materials.add(SULFITE_AND_THIOSULFATE_SALTS);
        materials.add(OXIMES);
        materials.add(POLYMERIZABLE_COMPOUNDS);
        materials.add(NOT_CHEMICALLY_REACTIVE);
        materials.add(INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION);
        materials.add(WATER_AND_AQUEOUS_SOLUTIONS);

        NUM_REACTIVE_GROUPS = integerChemTypesMap.size();
    }

    public static final int NUM_REACTIVE_GROUPS;

    public static Set<ChemTypes> getMaterials() {
        return materials;
    }

    public static Set<ChemTypes> getNums() {
        return numbers;
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
