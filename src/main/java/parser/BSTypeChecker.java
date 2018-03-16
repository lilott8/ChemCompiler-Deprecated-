package parser;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import chemical.epa.ChemTypes;
import parser.ast.AssignmentInstruction;
import parser.ast.BranchStatement;
import parser.ast.DetectStatement;
import parser.ast.Manifest;
import parser.ast.MixStatement;
import parser.ast.Module;
import parser.ast.RepeatStatement;
import parser.ast.SplitStatement;
import parser.ast.Stationary;
import shared.Step;
import shared.variable.Variable;
import symboltable.SymbolTable;
import typesystem.satsolver.strategies.SolverStrategy;
import typesystem.satsolver.strategies.Z3Strategy;

import static chemical.epa.ChemTypes.NAT;
import static chemical.epa.ChemTypes.REAL;

/**
 * @created: 2/27/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSTypeChecker extends BSVisitor implements TypeChecker {

    public static final String NL = System.lineSeparator();
    public static final String TAB = "\t";

    // Name of current working variable.
    private String name;
    // Associated types.
    private Set<ChemTypes> types = new HashSet<>();

    // How we solve constraints.
    private SolverStrategy z3 = new Z3Strategy();

    public BSTypeChecker() {
        super();

        StringBuilder sb = new StringBuilder();

        sb.append("; Initialize declares for chemtypes").append(NL);
        // Initialize the declares for the chemtrail objects.
        for (Map.Entry<Integer, ChemTypes> chemtype : ChemTypes.getIntegerChemTypesMap().entrySet()) {
            sb.append("(declare-const ").append(chemtype.getValue()).append(" Bool)").append(NL);
        }

        for (Map.Entry<String, Variable> entry : SymbolTable.INSTANCE.getSymbols().entrySet()) {
            sb.append("; Initialize declares for: ").append(SolverStrategy.getSMTName(entry.getValue().getName())).append(NL);
            for (Map.Entry<Integer, ChemTypes> types : ChemTypes.getIntegerChemTypesMap().entrySet()) {
                sb.append("(declare-const ").append(SolverStrategy.getSMTName(entry.getValue().getScopedName(), types.getValue())).append(" Bool)").append(NL);
            }
        }

        for (Map.Entry<String, Variable> i : SymbolTable.INSTANCE.getSymbols().entrySet()) {
            sb.append(this.buildAssertsForNumberMaterial(i.getValue()));
        }

        logger.info(sb.toString());
    }


    @Override
    public void solve() {
        logger.fatal("solveConstraints is commented out.");
        //this.z3.solveConstraints(statements, variables);
    }

    @Override
    public Step run() {
        //if (!this.z3.solveConstraints(statements, variables)) {
        //    throw new ChemTrailsException("Program is not type checkable.");
        //}
        return this;
    }

    @Override
    public String getName() {
        return this.getClass().getName();
    }

    /**
     * f0 -> <MODULE>
     * f1 -> Identifier()
     */
    @Override
    public BSVisitor visit(Module n) {
        return super.visit(n);
    }

    /**
     * f0 -> <STATIONARY>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Stationary n) {
        return super.visit(n);
    }

    /**
     * f0 -> <MANIFEST>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     */
    @Override
    public BSVisitor visit(Manifest n) {
        return super.visit(n);
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     */
    @Override
    public BSVisitor visit(AssignmentInstruction n) {
        return super.visit(n);
    }

    /**
     * f0 -> <MIX>
     * f1 -> PrimaryExpression()
     * f2 -> <WITH>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public BSVisitor visit(MixStatement n) {
        return super.visit(n);
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> IntegerLiteral()
     */
    @Override
    public BSVisitor visit(SplitStatement n) {
        return super.visit(n);
    }

    /**
     * f0 -> <DETECT>
     * f1 -> PrimaryExpression()
     * f2 -> <ON>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     */
    @Override
    public BSVisitor visit(DetectStatement n) {
        return super.visit(n);
    }

    /**
     * f0 -> <REPEAT>
     * f1 -> IntegerLiteral()
     * f2 -> <TIMES>
     * f3 -> <LBRACE>
     * f4 -> ( Statement() )+
     * f5 -> <RBRACE>
     */
    @Override
    public BSVisitor visit(RepeatStatement n) {
        return super.visit(n);
    }

    /**
     * f0 -> <IF>
     * f1 -> <LPAREN>
     * f2 -> Expression()
     * f3 -> <RPAREN>
     * f4 -> <LBRACE>
     * f5 -> ( Statement() )+
     * f6 -> <RBRACE>
     * f7 -> ( ElseIfStatement() )*
     * f8 -> ( ElseStatement() )?
     */
    @Override
    public BSVisitor visit(BranchStatement n) {
        return super.visit(n);
    }

    /**
     * This builds the (assert (not (or (= NAT true) (= REAL true))) Or the opposite, for each
     * variable.
     *
     * @param v input variable
     *
     * @return SMT String
     */
    private String buildAssertsForNumberMaterial(Variable v) {
        StringBuilder sb = new StringBuilder();
        boolean isMat;

        Set<ChemTypes> numbers = new HashSet<>(ChemTypes.getNums());
        Set<ChemTypes> materials = new HashSet<>(ChemTypes.getMaterials());

        numbers.retainAll(v.getTypes());
        materials.retainAll(v.getTypes());

        // If we have an intersection, i.e. NAT || REAL appear in both sets,
        // And the typing constraints are > 2 (more than NAT & REAL), then
        // This program is untypeable.
        if (!numbers.isEmpty() && !materials.isEmpty()) {
            sb.append("; Kill the type typesystem for ").append(v.getName()).append(NL);
            sb.append("(assert (= true false))").append(NL);
            return sb.toString();
        }

        // Otherwise we assume correctness.
        if (v.getTypes().contains(REAL) || v.getTypes().contains(NAT)) {
            sb.append("; ").append(SolverStrategy.getSMTName(v.getName())).append(" is a NUMBER").append(NL);
            isMat = false;
        } else {
            sb.append("; ").append(SolverStrategy.getSMTName(v.getName())).append(" is a MAT").append(NL);
            isMat = true;
        }

        sb.append("(assert").append(NL);
        if (isMat) {
            sb.append(TAB).append("(not").append(NL);
        }
        sb.append(TAB + TAB).append("(or").append(NL)
                .append(TAB + TAB + TAB).append("(= ").append(SolverStrategy.getSMTName(v.getScopedName(), REAL))
                .append(" true)").append(NL)
                .append(TAB + TAB + TAB).append("(= ").append(SolverStrategy.getSMTName(v.getScopedName(), NAT))
                .append(" true)").append(NL);
        if (isMat) {
            sb.append(TAB + TAB).append(")").append(NL);
        }
        sb.append(TAB).append(")").append(NL).append(")").append(NL);

        return sb.toString();
    }
}
