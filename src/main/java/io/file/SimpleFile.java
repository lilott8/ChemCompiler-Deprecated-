package io.file;

import com.google.common.collect.Table;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Map;
import java.util.Set;

import config.ConfigFactory;
import config.InferenceConfig;
import reactivetable.Chemical;

/**
 * @created: 10/2/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SimpleFile extends FileHandler {


    public static final Logger logger = LogManager.getLogger(ThreadedFile.class);

    public SimpleFile() {
        super();
    }

    public SimpleFile(String name) {
        super(name);
    }

    @Override
    public void writeTable(Table<Integer, Integer, Set<Integer>> table) {
        this.write(table);
    }

    @Override
    public void push(String string) {
        this.write(string);
    }

    @Override
    public void sendDoneSignal() {
        this.closeFile();
    }

    @Override
    String getCurrentFile() {
        return String.format("%s%s_%d", this.outputDir, this.baseFile, this.fileNumber);
    }

    public void openFile() {
        try {
            this.writer = new BufferedWriter(new FileWriter(this.getCurrentFile()));
        } catch(IOException e) {
            logger.error(String.format("Error opening: %s", this.getCurrentFile()));
            logger.error(e.toString());
        }
    }
}
