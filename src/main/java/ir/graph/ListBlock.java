package ir.graph;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import ir.statements.Statement;

/**
 * @created: 3/13/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ListBlock {
    public Map<Integer, Statement> statements = new LinkedHashMap<>();
}
