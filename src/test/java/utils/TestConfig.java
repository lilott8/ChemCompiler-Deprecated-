package utils;

import java.util.ArrayList;
import java.util.List;

import config.CommonConfig;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class TestConfig implements CommonConfig {

    List<String> files = new ArrayList<>();

    public TestConfig(String file) {
        files.add(file);
    }

    @Override
    public List<String> getFilesForCompilation() {
        return files;
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
}
