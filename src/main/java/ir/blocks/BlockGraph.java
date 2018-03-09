package ir.blocks;

import com.google.gson.internal.LinkedTreeMap;

import org.jgrapht.graph.AbstractBaseGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedPseudograph;
import org.jgrapht.io.ComponentNameProvider;
import org.jgrapht.io.DOTExporter;
import org.jgrapht.io.IntegerComponentNameProvider;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Map;

import javax.annotation.Nullable;

import config.ConfigFactory;
import ir.graph.SourceStatement;
import ir.graph.Statement;

/**
 * @created: 3/7/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BlockGraph {

    private AbstractBaseGraph<Statement, DefaultEdge> basicBlocks = new DirectedPseudograph<>(DefaultEdge.class);
    private Block currentBlock = new Block();
    private Map<Integer, Block> blockMap = new LinkedTreeMap<>();
    private Deque<Block> blockQueue = new ArrayDeque<>();

    public void addToBlock(Statement statement) {
        this.basicBlocks.addVertex(statement);
        if (this.currentBlock.getStatements().size() >= 1) {
            this.basicBlocks.addEdge(this.currentBlock.getLastStatement(), statement);
        }
        this.currentBlock.addStatement(statement);
    }

    public void newBasicBlock(Statement statement) {
        this.blockMap.put(this.currentBlock.getId(), this.currentBlock);
        this.basicBlocks.addVertex(statement);
        this.basicBlocks.addEdge(this.currentBlock.getLastStatement(), statement);
        // Save the block if we need it.
        this.blockQueue.push(this.currentBlock);
        this.currentBlock = new Block(statement);
    }

    public void newBranchBlock() {
        this.newBranchBlock(new SourceStatement());
    }

    public void newBranchBlock(Statement statement) {
        Block temp = new Block();
        this.basicBlocks.addVertex(statement);
        temp.addStatement(statement);
        this.basicBlocks.addEdge(this.currentBlock.getLastStatement(), temp.getLastStatement());
        this.blockQueue.push(this.currentBlock);
        this.currentBlock = temp;
    }

    public void addEdge(Statement source, Statement destination) {
        this.basicBlocks.addEdge(source, destination);
    }

    public void endBranchBlock() {
        Block temp = new Block();
    }

    public void pointsBackTo(Statement statement) {
        Block pointsTo = this.getBlockByStatement(statement);
        if (pointsTo != null) {
            this.basicBlocks.addVertex(statement);
            this.basicBlocks.addEdge(pointsTo.getLastStatement(), statement);
        }
    }

    @Nullable
    private Block getBlockByStatement(Statement statement) {
        Block ret = null;
        for (Map.Entry<Integer, Block> entry : this.blockMap.entrySet()) {
            for (Statement s : entry.getValue().getStatements()) {
                if (s.getId() == statement.getId()) {
                    ret = entry.getValue();
                }
            }
        }
        return ret;
    }

    public void newBasicBlock() {

    }

    public void writeToDisk() {
        try (FileOutputStream fileOutputStream = new FileOutputStream(ConfigFactory.getConfig().getOutputDir() + "graph.dot");
             OutputStreamWriter writer = new OutputStreamWriter(fileOutputStream, "UTF-8")) {
            ComponentNameProvider<Statement> vertexId = v -> v.getIdAsString();
            ComponentNameProvider<Statement> vertexName = v -> v.getName();
            ComponentNameProvider<DefaultEdge> edgeId = new IntegerComponentNameProvider<>();
            DOTExporter<Statement, DefaultEdge> exporter = new DOTExporter<>(vertexId, vertexName, edgeId, null, null);
            exporter.exportGraph(this.basicBlocks, writer);
        } catch (IOException e) {
            //logger.fatal(e.getMessage());
            e.printStackTrace();
        }
    }
}
