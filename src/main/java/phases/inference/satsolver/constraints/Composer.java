package phases.inference.satsolver.constraints;

import org.apache.commons.lang3.StringUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.HashSet;
import java.util.Set;

import phases.inference.elements.Instruction;
import phases.inference.elements.Variable;
import typesystem.epa.ChemTypes;

/**
 * @created: 9/12/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Composer {

    String compose(Instruction instruction);
    String compose(Variable variable);
}
