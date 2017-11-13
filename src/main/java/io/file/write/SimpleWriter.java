package io.file.write;

import com.google.common.collect.Table;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.IOException;
import java.util.Set;

/**
 * @created: 10/2/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class SimpleWriter extends FileWriter {

    public static final Logger logger = LogManager.getLogger(ThreadedWriter.class);

    public SimpleWriter() {
        super();
    }

    public SimpleWriter(String name) {
        super(name);
    }

    public SimpleWriter(String name, boolean useNumbering) {
        super(name, useNumbering);
    }

    @Override
    public void writeTable(Table<Integer, Integer, Set<Integer>> table) {
        this.write(table);
    }

    @Override
    public void push(String string) {
        super.write(string);
    }

    @Override
    public void sendDoneSignal() {
        super.closeFile();
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
