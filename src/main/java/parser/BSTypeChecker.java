package parser;

import java.util.HashSet;
import java.util.Set;

import chemical.epa.ChemTypes;
import chemical.identification.IdentifierFactory;
import ir.TypedInstruction;
import shared.Step;
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

    // Ability to identify stuff.
    private chemical.identification.Identifier identifier = IdentifierFactory.getIdentifier();

    // How we solve constraints.
    private SolverStrategy z3 = new Z3Strategy();

    @Override
    public void solve() {
        this.z3.solveConstraints(instructions, variables);
    }

    @Override
    public Step run() {
        return this;
    }

    @Override
    public String getName() {
        return this.getClass().getName();
    }
}
