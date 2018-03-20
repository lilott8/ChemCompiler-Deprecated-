package chemical;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import chemical.classification.Classifier;
import chemical.classification.ClassifierFactory;
import chemical.combinator.Combiner;
import chemical.combinator.CombinerFactory;
import chemical.epa.EpaManager;
import chemical.identification.Identifier;
import chemical.identification.IdentifierFactory;
import compilation.datastructures.node.InstructionNode;
import config.ConfigFactory;
import config.InferenceConfig;
import shared.substances.BaseCompound;
import translators.typesystem.TypeSystemTranslator;
import variable.Variable;

/**
 * A monolithic implement for managing the three phases for running the typesystem.
 * This encapsulates the identification, classification and combination phases.
 * The input is a serialized object from one of our library files that run this
 * project
 */
public class TypeSystem {

    public static final Logger logger = LogManager.getLogger(TypeSystem.class);

    private Map<String, List<String>> instructionInputs = new HashMap<String, List<String>>();
    private Map<String, BaseCompound> resolvedVariables = new HashMap<>();
    private Map<String, BaseCompound> cache = new HashMap<>();
    private TypeSystemTranslator translator;
    private Identifier identifier;
    private Combiner combiner;
    private Classifier classifier;


    public TypeSystem() {
        InferenceConfig config = ConfigFactory.getConfig();
        this.identifier = IdentifierFactory.getIdentifier();
        this.combiner = CombinerFactory.getCombiner();
        this.classifier = ClassifierFactory.getClassifier();
    }

    public TypeSystem loadTranslator(String file) {
        translator = TypeSystemTranslator.readFromFile(file);
        return this;
    }

    public TypeSystem loadManual(String file) {
        throw new NotImplementedException();
    }

    /**
     * the run implementation of our system, this runs through the three phases for the generated chemical interaction
     * statements
     */
    public void run() {
        // find and identify the literal compounds
        this.buildMaps();
        // classify the compounds if needed
        this.classifyCompounds();
        // validate the compound interactions
        this.validateInteractions();
    }

    /**
     * Take the chemical interaction statements and build the ordered operations that have inputs and resolve them
     * appropriately for running through the phases
     */
    private void buildMaps() {
        for (InstructionNode i : this.translator.getInstructions()) {
            String output = "";
            // this will only ever have one element.  Thus we get it and use it for the output
            // variable to cache what
            for (Map.Entry<String, Variable> o : i.getInstruction().getOutputs().entrySet()) {
                output = o.getKey();
            }
            if (!instructionInputs.containsKey(output)) {
                instructionInputs.put(output, new ArrayList<String>());
            }
            for (Map.Entry<String, Variable> in : i.getInstruction().getInputs().entrySet()) {
                for (ChemicalResolution cr : this.translator.getTable().getResolution(in.getKey()).getReferences()) {
                    if (cr.IsLiteral() && !this.instructionInputs.containsKey(cr.getName())) {
                        resolvedVariables.put(in.getKey(), this.identifier.identifyCompound(cr.getName()));
                    }
                }
                instructionInputs.get(output).add(in.getKey());
            }
        }
        //logger.info(this.translator.toString());
        logger.trace("getInstruction Inputs: " + instructionInputs);
        logger.trace("Resolved Variables: " + resolvedVariables);
    }

    /**
     * Wrapper function for classifying all the compounds.
     */
    public void classifyCompounds() {
        // classify the compounds we don't have reactive groups for
        for (Map.Entry<String, BaseCompound> entry : this.resolvedVariables.entrySet()) {
            if (entry.getValue().getReactiveGroups().size() < 1) {
                //logger.warn("We need to classify: " + entry.getValue().getName());
                entry.getValue().addReactiveGroup(this.classifier.classify(entry.getValue()));
            }
        }
    }

    /**
     * Validate that we can mix the compounds together through the EPA mixture matrix and
     * then attempt to mix anything that passes validation.
     */
    public void validateInteractions() {
        for (Map.Entry<String, List<String>> entry : this.instructionInputs.entrySet()) {
            logger.debug(entry);
            logger.warn("[validateInteraction] Using an unsafe way to get chemicals");
            BaseCompound a = this.resolveInput(entry.getValue().get(0));
            BaseCompound b = this.resolveInput(entry.getValue().get(1));
            EpaManager.INSTANCE.validate(a, b);
            BaseCompound compound = this.combiner.combine(a, b);
            this.cache.put(entry.getKey(), compound);
        }
    }

    /**
     * A helper function that that allows us to search for a resolution
     * of a string.  It allows the system to know exactly what a
     * reference is comprise of
     */
    private BaseCompound resolveInput(String s) {
        logger.info("Given: " + s);
        // always look in the cache first!
        if (this.cache.containsKey(s)) {
            logger.info("Found: " + cache.get(s).getName());
            return this.cache.get(s);
        }
        // otherwise we need to look at all the
        // variables that we have until we find a
        // legitimate resolution
        while (!resolvedVariables.containsKey(s)) {
            for (String n : instructionInputs.get(s)) {
                if (resolvedVariables.containsKey(n)) {
                    logger.info("Found: " + resolvedVariables.get(n).getName());
                    return resolvedVariables.get(n);
                }
            }
        }
        logger.trace("Found: " + resolvedVariables.get(s).getName());
        return resolvedVariables.get(s);
    }
}
