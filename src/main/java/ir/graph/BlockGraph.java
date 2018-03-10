package ir.graph;

import com.google.gson.internal.LinkedTreeMap;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jgrapht.Graph;
import org.jgrapht.graph.AbstractBaseGraph;
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
import ir.statements.SourceStatement;
import ir.statements.Statement;

/**
 * @created: 3/7/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BlockGraph {

    public static final Logger logger = LogManager.getLogger(BlockGraph.class);

    private AbstractBaseGraph<Statement, Edge> graph = new DirectedPseudograph<>(Edge.class);
    private Block currentBlock = new Block();
    private Map<Integer, Block> blockMap = new LinkedTreeMap<>();
    private Deque<Block> blockQueue = new ArrayDeque<>();

    public static void writeToDisk(Map<String, BlockGraph> graphs) {
        try (FileOutputStream fileOutputStream = new FileOutputStream(ConfigFactory.getConfig().getOutputDir() + "statements.dot");
             OutputStreamWriter writer = new OutputStreamWriter(fileOutputStream, "UTF-8")) {
            ComponentNameProvider<Statement> vertexId = v -> v.getIdAsString();
            ComponentNameProvider<Statement> vertexName = v -> v.getName();
            ComponentNameProvider<Edge> edgeId = new IntegerComponentNameProvider<>();
            DOTExporter<Statement, Edge> exporter = new DOTExporter<>(vertexId, vertexName, edgeId, null, null);
            for (Map.Entry<String, BlockGraph> entry : graphs.entrySet()) {
                logger.info(entry.getKey());
                exporter.exportGraph(entry.getValue().getGraph(), writer);
            }
        } catch (IOException e) {
            //logger.fatal(e.getMessage());
            e.printStackTrace();
        }
    }

    public static void writeToDisk(Graph<Statement, Edge> graph) {
        try (FileOutputStream fileOutputStream = new FileOutputStream(ConfigFactory.getConfig().getOutputDir() + "statements.dot");
             OutputStreamWriter writer = new OutputStreamWriter(fileOutputStream, "UTF-8")) {
            ComponentNameProvider<Statement> vertexId = v -> v.getIdAsString();
            ComponentNameProvider<Statement> vertexName = v -> v.getName();
            ComponentNameProvider<Edge> edgeId = new IntegerComponentNameProvider<>();
            DOTExporter<Statement, Edge> exporter = new DOTExporter<>(vertexId, vertexName, edgeId, null, null);
            exporter.exportGraph(graph, writer);
        } catch (IOException e) {
            //logger.fatal(e.getMessage());
            e.printStackTrace();
        }
    }

    public Statement firstStatement() {
        return this.blockQueue.peekFirst().getLeader();
    }

    public Statement finalStatement() {
        return this.blockQueue.peekLast().getLastStatement();
    }

    public void newBranchBlock() {
        this.newBranchBlock(new SourceStatement());
    }

    public void addToBlock(Statement statement) {
        this.graph.addVertex(statement);
        if (this.currentBlock.getStatements().size() >= 1) {
            this.graph.addEdge(this.currentBlock.getLastStatement(), statement);
        }
        this.currentBlock.addStatement(statement);
    }

    public void newBasicBlock(Statement statement) {
        this.blockMap.put(this.currentBlock.getId(), this.currentBlock);
        this.graph.addVertex(statement);
        this.graph.addEdge(this.currentBlock.getLastStatement(), statement);
        // Save the block if we need it.
        this.blockQueue.push(this.currentBlock);
        this.currentBlock = new Block(statement);
    }

    /**
     * This creates a straggled blog,
     * It is up to the developer to connect
     * it to the statements.
     *
     * @param statement statement to be added to statements.
     */
    public void newElseBlock(Statement statement) {
        Block temp = new Block();
        this.graph.addVertex(statement);
        temp.addStatement(statement);
        this.blockMap.put(this.currentBlock.getId(), this.currentBlock);
        this.blockQueue.add(this.currentBlock);
        this.currentBlock = temp;
    }

    /**
     * Create and connect a new block.
     * This case handles the true statement.
     * Use @function newElseBlock to account
     * For the false case.
     *
     * @param statement statement to be added to the statements.
     */
    public void newBranchBlock(Statement statement) {
        Block temp = new Block();
        this.graph.addVertex(statement);
        temp.addStatement(statement);
        this.graph.addEdge(this.currentBlock.getLastStatement(), temp.getLastStatement());
        this.blockMap.put(this.currentBlock.getId(), this.currentBlock);
        this.blockQueue.push(this.currentBlock);
        this.currentBlock = temp;
    }

    /**
     * Add an edge between graph/statements.
     * @param source
     * @param destination
     */
    public void addEdge(Statement source, Statement destination) {
        this.graph.addEdge(source, destination);
    }

    /**
     * Remove an edge, used for updating loops/branches.
     *
     * @param source      source of edge.
     * @param destination destination of edge.
     */
    public void removeEdge(Statement source, Statement destination) {
        this.graph.removeEdge(source, destination);
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

    public void updateStatement(Statement newVertex, Statement oldVertex) {
        this.graph.addVertex(newVertex);
        for (Edge edge : this.graph.outgoingEdgesOf(oldVertex)) {
            this.graph.addEdge(newVertex, this.graph.getEdgeTarget(edge), edge);
        }
        for (Edge edge : this.graph.incomingEdgesOf(oldVertex)) {
            this.graph.addEdge(this.graph.getEdgeTarget(edge), newVertex, edge);
        }
        this.graph.removeVertex(oldVertex);
    }

    public void pointsBackTo(Statement statement) {
        Block pointsTo = this.getBlockByStatement(statement);
        if (pointsTo != null) {
            this.graph.addVertex(statement);
            this.graph.addEdge(pointsTo.getLastStatement(), statement);
        }
    }

    public Graph<Statement, Edge> getGraph() {
        return this.graph;
    }
}
