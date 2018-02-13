package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import parser.ast.AssignmentInstruction;
import parser.ast.BSProgram;
import parser.ast.BranchStatement;
import parser.ast.DetectStatement;
import parser.ast.DrainStatement;
import parser.ast.FalseLiteral;
import parser.ast.Function;
import parser.ast.HeatStatement;
import parser.ast.IntegerLiteral;
import parser.ast.Manifest;
import parser.ast.MatLiteral;
import parser.ast.MixStatement;
import parser.ast.Module;
import parser.ast.NatLiteral;
import parser.ast.Node;
import parser.ast.PrimaryExpression;
import parser.ast.RealLiteral;
import parser.ast.RepeatStatement;
import parser.ast.SplitStatement;
import parser.ast.Stationary;
import parser.ast.TrueLiteral;
import parser.visitor.GJNoArguDepthFirst;
import phases.inference.satsolver.strategies.NewZ3Strategy;
import phases.inference.satsolver.strategies.SolverStrategy;
import phases.inference.satsolver.strategies.Z3Strategy;
import shared.Step;
import shared.Strategy;
import symboltable.SymbolTable;
import typesystem.combinator.Combiner;
import typesystem.combinator.CombinerFactory;
import typesystem.epa.ChemTypes;
import typesystem.identification.Identifier;
import typesystem.identification.IdentifierFactory;

import static typesystem.epa.ChemTypes.BOOL;
import static typesystem.epa.ChemTypes.MAT;
import static typesystem.epa.ChemTypes.MODULE;
import static typesystem.epa.ChemTypes.NAT;

/**
 * @created: 11/30/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSTypeChecker extends GJNoArguDepthFirst<BSTypeChecker> implements Step, TypeChecker {

    public static final Logger logger = LogManager.getLogger(BSTypeChecker.class);

    private static final String INTEGER = "INTEGER";
    private static final String BOOLEAN = "BOOLEAN";
    private static final String REAL = "REAL";
    private int realId = 0;
    private int booleanId = 0;
    private int integerId = 0;

    // The symbol table
    private SymbolTable symbolTable;
    // Name of variable.
    private String name;
    // Types associated with a variable.
    private Set<ChemTypes> types;
    // Typing constraints of variables.
    private Map<String, Set<ChemTypes>> typingConstraints = new HashMap<>();

    private Identifier identifier = IdentifierFactory.getIdentifier();
    private Combiner combiner = CombinerFactory.getCombiner();

    private Map<String, Set<ChemTypes>> typeInference = new LinkedHashMap<>();
    private SolverStrategy z3 = new Z3Strategy();
    private NewZ3Strategy newZ3 = new NewZ3Strategy();

    public BSTypeChecker(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    @Override
    public String getName() {
        return "BSTypeChecker";
    }

    @Override
    public Step run() {
        return this;
    }

    public void solve() {
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     * Depending on what the Expression evaluates to,
     *  This will dictate what the assignment is.
     */
    @Override
    public BSTypeChecker visit(AssignmentInstruction n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <MODULE>
     * f1 -> Identifier()
     * Does not apply
     */
    @Override
    public BSTypeChecker visit(Module n) {
        // super.visit(n);
        n.f1.accept(this);
        this.typeInference.put(this.name, new HashSet<>());
        this.typeInference.get(this.name).add(MODULE);
        return this;
    }

    /**
     * f0 -> <STATIONARY>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     * F_1 = MAT
     */
    @Override
    public BSTypeChecker visit(Stationary n) {
        // super.visit(n);
        // Get the name first
        n.f2.accept(this);
        if (n.f1.present()) {
            n.f1.accept(this);
            if (this.types.isEmpty()) {
                this.types.addAll(this.identifier.identifyCompoundForTypes(this.name));
            }
        }

        this.typeInference.put(this.name, new HashSet<>());
        this.typeInference.get(this.name).addAll(this.types);
        this.types.clear();
        return this;
    }

    /**
     * f0 -> <MANIFEST>
     * f1 -> ( TypingList() )?
     * f2 -> PrimaryExpression()
     * F_1 = MAT
     */
    @Override
    public BSTypeChecker visit(Manifest n) {
        // super.visit(n);
        n.f2.accept(this);
        if (n.f1.present()) {
            n.f1.accept(this);
            if (this.types.isEmpty()) {
                this.types.addAll(this.identifier.identifyCompoundForTypes(this.name));
            }
        }

        this.typeInference.put(this.name, new HashSet<>());
        this.typeInference.get(this.name).addAll(this.types);
        this.types.clear();
        return this;
    }

    /**
     * f0 -> <FUNCTION>
     * f1 -> Identifier()
     * f2 -> <LPAREN>
     * f3 -> ( FormalParameterList() )*
     * f4 -> <RPAREN>
     * f5 -> ( <COLON> TypingList() )?
     * f6 -> <LBRACE>
     * f7 -> ( Statement() )*
     * f8 -> ( <RETURN> Expression() )?
     * f9 -> <RBRACE>
     * T = {MAT, NAT, REAL}
     */
    @Override
    public BSTypeChecker visit(Function n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <MIX>
     * f1 -> PrimaryExpression()
     * f2 -> <WITH>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     * F_0 = Mat (assignment)
     * F_1 = Mat
     * F_3 = Mat
     * F_4 = Nat
     */
    @Override
    public BSTypeChecker visit(MixStatement n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <SPLIT>
     * f1 -> PrimaryExpression()
     * f2 -> <INTO>
     * f3 -> IntegerLiteral()
     * F_1 = Mat
     * F_3 = Nat
     */
    @Override
    public BSTypeChecker visit(SplitStatement n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     * F_1 = Mat
     */
    @Override
    public BSTypeChecker visit(DrainStatement n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <HEAT>
     * f1 -> PrimaryExpression()
     * f2 -> <AT>
     * f3 -> IntegerLiteral()
     * f4 -> ( <FOR> IntegerLiteral() )?
     * F_1 = Mat
     * F_3 = Real
     * F_4 = Nat
     */
    @Override
    public BSTypeChecker visit(HeatStatement n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <DETECT>
     * f1 -> PrimaryExpression()
     * f2 -> <ON>
     * f3 -> PrimaryExpression()
     * f4 -> ( <FOR> IntegerLiteral() )?
     * F_1 = N/A
     * F_3 = Mat
     * F_4 = Nat
     */
    @Override
    public BSTypeChecker visit(DetectStatement n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <REPEAT>
     * f1 -> IntegerLiteral()
     * f2 -> <TIMES>
     * f3 -> <LBRACE>
     * f4 -> Statement()
     * f5 -> <RBRACE>
     * F_1 = Nat/Real
     */
    @Override
    public BSTypeChecker visit(RepeatStatement n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE_IF> <LPAREN> Expression() <RPAREN> <LBRACE> Statement() <RBRACE>
     * | <ELSE> <LBRACE> Statement() <RBRACE>
     * F_0 = Nat
     */
    @Override
    public BSTypeChecker visit(BranchStatement n) {
        // super.visit(n);

        return this;
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    @Override
    public BSTypeChecker visit(parser.ast.Identifier n) {
        // super.visit(n);

        if (this.types.contains(ChemTypes.REAL)) {
            this.name = String.format("%s_%d", REAL, realId++);
        } else if (this.types.contains(NAT)) {
            this.name = String.format("%s_%d", INTEGER, integerId++);
        } else if (this.types.contains(BOOL)) {
            this.name = String.format("%s_%d", BOOLEAN, booleanId++);
        } else {
            this.name = n.f0.toString();
        }

        return this;
    }

    /**
     * f0 -> <INTEGER_LITERAL>
     */
    @Override
    public BSTypeChecker visit(IntegerLiteral n) {
        // super.visit(n);
        this.types.add(NAT);
        return this;
    }

    /**
     * f0 -> <NAT>
     */
    @Override
    public BSTypeChecker visit(NatLiteral n) {
        // super.visit(n);
        this.types.add(NAT);
        return this;
    }

    /**
     * f0 -> <MAT>
     */
    @Override
    public BSTypeChecker visit(MatLiteral n) {
        // super.visit(n);
        this.types.add(MAT);
        logger.info("You are using naive mat, right now");
        // this.types.addAll(this.identifier.identifyCompoundForTypes(this.name));
        return this;
    }

    /**
     * f0 -> <REAL>
     */
    @Override
    public BSTypeChecker visit(RealLiteral n) {
        // super.visit(n);
        this.types.add(ChemTypes.REAL);
        return this;
    }

    /**
     * f0 -> <TRUE>
     */
    @Override
    public BSTypeChecker visit(TrueLiteral n) {
        // super.visit(n);
        this.types.add(BOOL);
        return this;
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public BSTypeChecker visit(FalseLiteral n) {
        this.types.add(BOOL);
        return this;
    }
}
