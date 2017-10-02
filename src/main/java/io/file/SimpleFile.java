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

    public SimpleFile(String name, boolean useNumbering) {
        super(name, useNumbering);
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
    public void flush() {
        try {
            this.writer.flush();
        } catch(IOException e) {
            logger.error("Could not flush to disk.");
            logger.error(e);
        }
    }
}
