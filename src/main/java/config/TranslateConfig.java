package config;

import java.util.Map;
import java.util.Set;

import Translators.Translator;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface TranslateConfig {

    String MFSIM = "mfsim";
    String TYPESYSTEM = "typesystem";

    Map<String, Translator> getAllTranslations();
    boolean translationEnabled(String translator);
    boolean translationsEnabled();
    String getOutputDir();
}
