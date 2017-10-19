package config;

import java.util.List;

/**
 * @created: 9/5/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface CommonConfig {

    String getOutputDir();
    boolean clean();
    List<String> getFilesForCompilation();

    boolean isDebug();
    int getNumberOfThreads();
}
