package config;

import java.util.Map;

import translators.Translator;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface TranslateConfig extends CommonConfig {

    String MFSIM = "mfsim";
    String TYPESYSTEM = "typesystem";

    Map<String, Translator> getAllTranslations();

    boolean translationEnabled(String translator);

    boolean translationsEnabled();

    String getOutputDir();
}
