package io.file.write;


import com.google.common.collect.Table;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.Set;

import config.ConfigFactory;
import config.InferenceConfig;

/**
 * @created: 10/2/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public abstract class FileWriter extends Thread {
    protected String outputDir;
    protected String baseFile;
    protected final int MAX_WRITES = 100;
    protected BufferedWriter writer;
    protected int fileNumber = 1;
    protected long invalid = 0;
    protected boolean useNumbering = false;
    private Logger logger = LogManager.getLogger(FileWriter.class);

    //abstract void openFile();
    public abstract void push(String string);
    public abstract void sendDoneSignal();
    public abstract void writeTable(Table<Integer, Integer, Set<Integer>> table);
    public abstract void flush();

    {
        InferenceConfig config = ConfigFactory.getConfig();
        this.outputDir = config.getOutputDir();
    }

    protected FileWriter() {
        this.baseFile = "test";
        this.openFile();
    }

    protected FileWriter(String fileName) {
        this.baseFile = fileName;
        this.openFile();
    }

    protected FileWriter(String fileName, boolean useNumbering) {
        this.baseFile = fileName;
        this.useNumbering = useNumbering;
        this.openFile();
    }

    public void changeFile() {
        this.closeFile();
        this.openFile();
        // logger.trace("Changing files: " + this.getCurrentFile());
    }

    protected void openFile() {
        try {
            this.writer = new BufferedWriter(new java.io.FileWriter(this.getCurrentFile()));
        } catch(IOException e) {
            logger.error(String.format("Error opening: %s", this.getCurrentFile()));
            logger.error(e.toString());
        }
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

    protected String getCurrentFile() {
        if (this.useNumbering) {
            return String.format("%s%s_%d", this.outputDir, this.baseFile, this.fileNumber);
        } else {
            return this.outputDir + this.baseFile;
        }
    }

    public boolean write(int number) {
        return this.write(Integer.toString(number));
    }

    public boolean write(long number) {
        return this.write(Long.toString(number));
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
