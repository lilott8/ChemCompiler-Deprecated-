package shared.properties;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.Set;

import chemical.epa.ChemTypes;

/**
 * @created: 7/1/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Conditional extends Property {

    public static final Logger logger = LogManager.getLogger(Conditional.class);

    public Conditional(String name, String units, float value) {
        super(name, units, value);
    }

    public Conditional(String name, String units, float value, Set<ChemTypes> types) {
        super(name, units, value, types);
    }

    @Override
    public String buildDeclaration() {
        logger.fatal("Conditionals don't work like that.");
        throw new NotImplementedException();
    }

    @Override
    public String buildUsage() {
        logger.fatal("Conditionals don't work like that.");
        throw new NotImplementedException();
    }
}
