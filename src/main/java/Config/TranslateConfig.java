package Config;

import java.util.Map;

import Translators.Translator;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface TranslateConfig {

    Translator getTranslationByName(String name);
    Map<String, Translator> getAllTranslations();
    boolean translationEnabled(String name);
    boolean translationsEnabled();
}
