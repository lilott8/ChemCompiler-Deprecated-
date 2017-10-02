package io.file;


import com.google.common.collect.Table;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.Set;

import chemaxon.jep.function.In;
import config.ConfigFactory;
import config.InferenceConfig;

/**
 * @created: 10/2/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class FileHandler extends Thread {
    protected String outputDir;
    protected String baseFile;
    protected final int MAX_WRITES = 100;
    protected BufferedWriter writer;
    protected int fileNumber = 1;
    protected long invalid = 0;
    private Logger logger = LogManager.getLogger(FileHandler.class);

    abstract void openFile();
    public abstract void push(String string);
    public abstract void sendDoneSignal();
    public abstract void writeTable(Table<Integer, Integer, Set<Integer>> table);
    abstract String getCurrentFile();

    {
        InferenceConfig config = ConfigFactory.getConfig();
        this.outputDir = config.getOutputDir();
    }

    protected  FileHandler() {
        this.baseFile = "test";
        this.openFile();
    }

    protected FileHandler(String fileName) {
        this.baseFile = fileName;
        this.openFile();
    }

    public void changeFile() {
        this.closeFile();
        this.openFile();
        logger.info("Changing files: " + this.getCurrentFile());
    }

    protected void closeFile() {
        try {
            this.writer.close();
            // increment after close!
            this.fileNumber++;
        } catch(IOException e) {
            logger.error(String.format("Error closing: %s", this.getCurrentFile()));
            logger.error(e.toString());
        }
    }

    public boolean write(int number) {
        return this.write(Integer.toString(number));
    }

    public boolean write(String item) {
        try {
            this.writer.write(item);
            this.writer.newLine();
            return true;
        } catch(IOException e) {
            logger.error(String.format("Error writing to: %s", this.getCurrentFile()));
            logger.info("With data: " + item);
            logger.error(e.toString());
            return false;
        }
    }

    protected void write(Table<Integer, Integer, Set<Integer>> comboTable) {
        for (Table.Cell<Integer, Integer, Set<Integer>> cell: comboTable.cellSet()){
            StringBuilder sb = new StringBuilder();
            sb.append(cell.getRowKey()).append("|").append(cell.getColumnKey()).append("|");
            for (int type : cell.getValue()) {
                sb.append(type).append("_");
            }
            this.write(sb.toString());
        }
    }
}
