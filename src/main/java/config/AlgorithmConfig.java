package config;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
interface AlgorithmConfig extends CommonConfig {

    boolean runSSA();
    boolean runSSI();

}
