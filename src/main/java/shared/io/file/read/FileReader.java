package shared.io.file.read;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/**
 * @created: 10/9/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class FileReader {

    private static final Logger logger = LogManager.getLogger(FileReader.class);

    protected String fileName;
    protected BufferedReader handler;

    protected FileReader(String fileName) {
        this.fileName = fileName;
        this.open();
    }

    protected void open() {
        try {
            this.handler = new BufferedReader(new java.io.FileReader(this.fileName));
        } catch(Exception e) {
            logger.error("Error opening file.");
            logger.error(e);
        }
    }

    public String nextLine() {
        try {
            String line = this.handler.readLine();
            if (line == null) {
                return null;
            }
            return line;
        } catch(IOException e) {
            logger.error("Error reading line.");
            logger.error(e);
        }
        return null;
    }

    public List<String> allLines() {
        List<String> results = new ArrayList<>();
        String line;
        while((line = this.nextLine()) != null) {
            results.add(line);
        }

        return results;
    }

    public void close() {
        try {
            this.handler.close();
        } catch(Exception e) {
            logger.error("Error closing file.");
            logger.error(e);
        }
    }
}
