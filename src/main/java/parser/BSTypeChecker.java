package parser;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import parser.ast.Assignment;
import parser.ast.DetectInstruction;
import parser.ast.DrainInstruction;
import parser.ast.ElseIfStatement;
import parser.ast.FalseLiteral;
import parser.ast.FunctionDefinition;
import parser.ast.FunctionInvoke;
import parser.ast.HeatInstruction;
import parser.ast.IfStatement;
import parser.ast.IntegerLiteral;
import parser.ast.Manifest;
import parser.ast.MatLiteral;
import parser.ast.MixInstruction;
import parser.ast.Module;
import parser.ast.NatLiteral;
import parser.ast.RealLiteral;
import parser.ast.RepeatInstruction;
import parser.ast.SplitInstruction;
import parser.ast.Stationary;
import parser.ast.TrueLiteral;
import parser.visitor.GJNoArguDepthFirst;
import shared.variables.Variable;
import typesystem.elements.Formula;
import shared.variables.Term;
import typesystem.rules.Rule;
import typesystem.satsolver.strategies.SolverStrategy;
import typesystem.satsolver.strategies.Z3Strategy;
import shared.Step;
import symboltable.SymbolTable;
import chemical.epa.ChemTypes;
import chemical.identification.Identifier;
import chemical.identification.IdentifierFactory;

import static typesystem.rules.Rule.InstructionType.DRAIN;
import static typesystem.rules.Rule.InstructionType.LOOP;
import static typesystem.rules.Rule.InstructionType.MANIFEST;
import static typesystem.rules.Rule.InstructionType.STATIONARY;
import static chemical.epa.ChemTypes.BOOL;
import static chemical.epa.ChemTypes.MAT;
import static chemical.epa.ChemTypes.MODULE;
import static chemical.epa.ChemTypes.NAT;
import static chemical.epa.ChemTypes.NULL;

/**
 * @created: 11/30/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class BSTypeChecker extends GJNoArguDepthFirst<BSTypeChecker> implements Step, TypeChecker {

    public static final Logger logger = LogManager.getLogger(BSTypeChecker.class);

    // These are constants for naming scopes/constants.
    private static final String INTEGER = "INTEGER";
    private static final String BOOLEAN = "BOOLEAN";
    private static final String REAL = "REAL";
    private static final String REPEAT = "REPEAT";
    private static final String BRANCH = "BRANCH";
    // Needed for scoping names where the scope is "branch".
    private int scopeId = 0;

    // Keep track of the instruction id to input/outputs
    protected static Map<Integer, Formula> instructions = new LinkedHashMap<>();
    protected static Map<String, Variable> variables = new HashMap<>();

    private int realId = 0;
    private int booleanId = 0;
    private int integerId = 0;

    // The symbol table
    private SymbolTable symbolTable;

    // Name of variable.
    private String name;

    // Typing constraints of variables.
    private Formula instruction;

    // Set the type to be NULL, for now.
    private ChemTypes typeForName = NULL;
    private Identifier identifier = IdentifierFactory.getIdentifier();
    private SolverStrategy z3 = new Z3Strategy();


    public BSTypeChecker(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    private static void addInstruction(Formula i) {
        instructions.put(i.getId(), i);
    }

    public static Map<Integer, Formula> getInstructions() {
        return instructions;
    }

    public Map<String, Variable> getVariables() {
        return this.symbolTable.getSymbols();
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
        this.z3.solveConstraints(instructions, this.symbolTable.getSymbols());
    }

    /**
     * f0 -> ( TypingList() )*
     * f1 -> Identifier()
     * f2 -> <ASSIGN>
     * f3 -> Expression()
     * Depending on what the Expression evaluates to,
     * This will dictate what the assignment is.
     */
    @Override
    public BSTypeChecker visit(Assignment n) {
        // Get the expression done before we get the identifier.
        // That way we can set the appropriate instruction.
        n.f3.accept(this);
        // Once we have established the expression,
        // We can identify the identifier.
        n.f1.accept(this);
        Term term = new Term(this.name);
        if (n.f0.present()) {
            n.f0.accept(this);
            term.addTypingConstraint(this.typeForName);
        }
        switch (this.instruction.getType()) {
            case MIX:
            case SPLIT:
                term.addTypingConstraints(this.getTypingConstraints(term));
                this.instruction.addOutputVariable(term);
                break;
            case DETECT:
                term.addTypingConstraint(ChemTypes.REAL);
                this.instruction.addOutputVariable(term);
                break;
            case FUNCTION:
                // We need to see what the return type of a given function is.
                term.addTypingConstraints(this.symbolTable.getMethods().get(term.getName()).getTypes());
                this.instruction.addOutputVariable(term);
                break;
        }
        addVariable(term);
        addInstruction(this.instruction);
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
        this.instruction = new Formula(Rule.InstructionType.MODULE);

        Term term = new Term(this.name);
        term.addTypingConstraint(MODULE);
        addVariable(term);
        instruction.addInputVariable(term);
        addInstruction(this.instruction);

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
        this.instruction = new Formula(STATIONARY);




        Variable term = new Term(this.name);
        term.addTypingConstraints(this.getTypingConstraints(term));
        addVariable(term);
        this.instruction.addInputVariable(term);
        addInstruction(this.instruction);

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
        this.instruction = new Formula(MANIFEST);
        Term term = new Term(this.name);
        term.addTypingConstraints(this.getTypingConstraints(term));
        addVariable(term);
        this.instruction.addInputVariable(term);
        addInstruction(this.instruction);
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
    public BSTypeChecker visit(FunctionDefinition n) {
        // super.visit(n);
        n.f1.accept(this);
        Term term = new Term(this.name);

        if (n.f5.present()) {
            n.f5.accept(this);
            term.addTypingConstraint(this.typeForName);
        }

        addVariable(term);

        n.f7.accept(this);

        if (n.f8.present()) {
            n.f8.accept(this);
        }

        return this;
    }

    /**
     * f0 -> Identifier()
     * f1 -> <LPAREN>
     * f2 -> ( ExpressionList() )?
     * f3 -> <RPAREN>
     */
    @Override
    public BSTypeChecker visit(FunctionInvoke n) {
        // super.visit(n);
        // TODO: not quite sure what to do here.


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
    public BSTypeChecker visit(MixInstruction n) {
        // super.visit(n);
        this.instruction = new Formula(Rule.InstructionType.MIX);

        n.f1.accept(this);
        Term term = new Term(this.name);
        term.addTypingConstraints(this.getTypingConstraints(term));
        addVariable(term);
        this.instruction.addInputVariable(term);

        n.f3.accept(this);
        term = new Term(this.name);
        term.addTypingConstraints(this.getTypingConstraints(term));
        addVariable(term);
        this.instruction.addInputVariable(term);

        if (n.f4.present()) {
            n.f4.accept(this);
            term = new Term(this.name);
            term.addTypingConstraint(NAT);
            addVariable(term);
            this.instruction.addProperty(term);
        }

        // Guarantee that we set the output variable typing,
        // And help ensure that the name is set correctly.
        this.typeForName = MAT;
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
    public BSTypeChecker visit(SplitInstruction n) {
        // super.visit(n);
        n.f1.accept(this);
        Term term = new Term(this.name);
        term.addTypingConstraints(this.getTypingConstraints(term));
        addVariable(term);

        n.f3.accept(this);
        term = new Term(this.name);
        term.addTypingConstraint(NAT);
        addVariable(term);

        this.instruction.addProperty(term);

        // Set this so that the output type is correct.
        this.typeForName = MAT;
        return this;
    }

    /**
     * f0 -> <DRAIN>
     * f1 -> PrimaryExpression()
     * F_1 = Mat
     */
    @Override
    public BSTypeChecker visit(DrainInstruction n) {
        // super.visit(n);
        n.f1.accept(this);
        Term term = new Term(this.name);
        term.addTypingConstraints(this.getTypingConstraints(term));
        addVariable(term);

        this.instruction = new Formula(DRAIN);
        this.instruction.addInputVariable(term);

        addInstruction(this.instruction);

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
    public BSTypeChecker visit(HeatInstruction n) {
        // super.visit(n);
        n.f1.accept(this);
        Term term = new Term(this.name);
        term.addTypingConstraints(this.getTypingConstraints(term));
        addVariable(term);
        this.instruction.addInputVariable(term);

        n.f3.accept(this);
        term = new Term(this.name);
        term.addTypingConstraint(ChemTypes.REAL);
        addVariable(term);
        this.instruction.addProperty(term);

        if (n.f4.present()) {
            n.f4.accept(this);
            term = new Term(this.name);
            term.addTypingConstraint(NAT);
            addVariable(term);

            this.instruction.addProperty(term);
        }

        addInstruction(this.instruction);

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
    public BSTypeChecker visit(DetectInstruction n) {
        // super.visit(n);
        n.f1.accept(this);
        Term term = new Term(this.name);
        term.addTypingConstraints(this.getTypingConstraints(term));
        addVariable(term);
        this.instruction.addInputVariable(term);

        n.f3.accept(this);
        term = new Term(this.name);
        term.addTypingConstraint(NAT);
        addVariable(term);
        this.instruction.addInputVariable(term);

        if (n.f4.present()) {
            n.f4.accept(this);
            term = new Term(this.name);
            term.addTypingConstraint(NAT);
            addVariable(term);
            this.instruction.addProperty(term);
        }

        this.typeForName = NAT;
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
    public BSTypeChecker visit(RepeatInstruction n) {
        // super.visit(n);
        this.name = String.format("%s_%d", NAT, integerId++);
        Term term = new Term(this.name);
        term.addTypingConstraint(NAT);
        addVariable(term);
        this.instruction = new Formula(LOOP);
        this.instruction.addInputVariable(term);
        addInstruction(this.instruction);

        n.f4.accept(this);

        return this;
    }

    /**
     * f0 -> <IF>
     * f1 -> <LPAREN>
     * f2 -> Expression()
     * f3 -> <RPAREN>
     * f4 -> <LBRACE>
     * f5 -> Statement()
     * f6 -> <RBRACE>
     */
    @Override
    public BSTypeChecker visit(IfStatement n) {
        // super.visit(n);
        this.instruction = new Formula(Rule.InstructionType.BRANCH);
        this.name = String.format("%s_%d", NAT, integerId);
        Term term = new Term(this.name);
        term.addTypingConstraint(NAT);
        addVariable(term);
        this.instruction.addInputVariable(term);
        addInstruction(this.instruction);

        n.f5.accept(this);

        return this;
    }

    /**
     * f0 -> <ELSE_IF>
     * f1 -> <LPAREN>
     * f2 -> Expression()
     * f3 -> <RPAREN>
     * f4 -> <LBRACE>
     * f5 -> Statement()
     * f6 -> <RBRACE>
     */
    @Override
    public BSTypeChecker visit(ElseIfStatement n) {
        // super.visit(n);
        this.instruction = new Formula(Rule.InstructionType.BRANCH);
        this.name = String.format("%s_%d", NAT, integerId);
        Term term = new Term(this.name);
        term.addTypingConstraint(NAT);
        addVariable(term);
        this.instruction.addInputVariable(term);
        addInstruction(this.instruction);

        n.f5.accept(this);

        return this;
    }

    /**
     * f0 -> <IDENTIFIER>
     */
    @Override
    public BSTypeChecker visit(parser.ast.Identifier n) {
        // super.visit(n);
        switch (this.typeForName) {
            default:
            case MAT:
                this.name = n.f0.toString();
                break;
            case REAL:
                this.name = String.format("%s_%d", REAL, realId++);
                break;
            case NAT:
                this.name = String.format("%s_%d", INTEGER, integerId++);
                break;
            case BOOL:
                this.name = String.format("%s_%d", BOOLEAN, booleanId++);
                break;
        }
        this.typeForName = NULL;
        return this;
    }

    /**
     * f0 -> <INTEGER_LITERAL>
     */
    @Override
    public BSTypeChecker visit(IntegerLiteral n) {
        // super.visit(n);
        this.typeForName = NAT;
        this.name = String.format("%s_%d", INTEGER, integerId++);
        return this;
    }

    /**
     * f0 -> <NAT>
     */
    @Override
    public BSTypeChecker visit(NatLiteral n) {
        // super.visit(n);
        this.typeForName = NAT;
        return this;
    }

    /**
     * f0 -> <MAT>
     */
    @Override
    public BSTypeChecker visit(MatLiteral n) {
        // super.visit(n);
        this.typeForName = MAT;
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
        this.typeForName = ChemTypes.REAL;
        return this;
    }

    /**
     * f0 -> <TRUE>
     */
    @Override
    public BSTypeChecker visit(TrueLiteral n) {
        // super.visit(n);
        this.typeForName = BOOL;
        return this;
    }

    /**
     * f0 -> <FALSE>
     */
    @Override
    public BSTypeChecker visit(FalseLiteral n) {
        this.typeForName = BOOL;
        return this;
    }

    private Set<ChemTypes> getTypingConstraints(Variable t) {
        if (variables.containsKey(t.getName())) {
            return variables.get(t.getName()).getTypes();
        } else {
            return this.identifier.identifyCompoundForTypes(t.getName());
        }
    }

    private static void addVariable(Variable t) {
        if (!variables.containsKey(t.getName())) {
            variables.put(t.getName(), t);
        } else {
            if (variables.get(t.getName()).equals(t)) {
                logger.warn(String.format("%s is equal to %s", t, variables.get(t.getName())));
            }
        }
    }
}
