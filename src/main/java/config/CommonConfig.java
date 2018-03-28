package config;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface CommonConfig {

    String getOutputDir();

    boolean clean();

    String getInputFile();

    boolean checkForChemAxon();

    boolean isDebug();

    int getNumberOfThreads();

    boolean monitorResources();
}
