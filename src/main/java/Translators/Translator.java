package Translators;

import CompilerDataStructures.ControlFlowGraph.CFG;
import Config.TranslateConfig;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface Translator {
    Translator setConfig(TranslateConfig config);
    Translator runTranslation(CFG controlFlowGraph);
    void toFile(String output);
}
