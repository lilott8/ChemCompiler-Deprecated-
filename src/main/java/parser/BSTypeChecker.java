package parser;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import shared.Step;
import shared.errors.ChemTrailsException;
import symboltable.SymbolTable;
import typesystem.satsolver.strategies.SolverStrategy;
import typesystem.satsolver.strategies.Z3Strategy;

/**
 * @created: 2/27/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSTypeChecker extends BSVisitor implements TypeChecker {

    // Name of current working variable.
    private String name;
    // Associated types.
    private Set<ChemTypes> types = new HashSet<>();

    // How we solve constraints.
    private SolverStrategy z3 = new Z3Strategy();

    public BSTypeChecker(SymbolTable symbolTable) {
        super(symbolTable);
    }

    @Override
    public void solve() {
        logger.fatal("solveConstraints is commented out.");
        //this.z3.solveConstraints(instructions, variables);
    }

    @Override
    public Step run() {
        //if (!this.z3.solveConstraints(instructions, variables)) {
        //    throw new ChemTrailsException("Program is not type checkable.");
        //}
        return this;
    }

    @Override
    public String getName() {
        return this.getClass().getName();
    }
}
