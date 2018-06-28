package utils;

import config.CommonConfig;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TestConfig implements CommonConfig {

    String file;

    public TestConfig(String file) {
        this.file = file;
    }

    @Override
    public String getInputFile() {
        return file;
    }

    @Override
    public String getOutputDir() {
        return null;
    }

    @Override
    public boolean clean() {
        return false;
    }

    @Override
    public boolean isDebug() {
        return false;
    }

    @Override
    public int getNumberOfThreads() {
        return 0;
    }

    @Override
    public boolean monitorResources() {
        return false;
    }

    @Override
    public boolean checkForChemAxon() {
        return true;
    }

    public boolean printStatistics() {
        return false;
    }
}
