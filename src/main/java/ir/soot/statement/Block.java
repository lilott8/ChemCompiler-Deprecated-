package ir.soot.statement;

import java.util.List;

import ir.soot.instruction.Instruction;

/**
 * @created: 3/2/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Block extends Statement {


    @Override
    public List<Instruction> getTrueBranch() {
        return super.getTrueBranch();
    }

    @Override
    public List<Instruction> getFalseBranch() {
        return super.getTrueBranch();
    }
}
