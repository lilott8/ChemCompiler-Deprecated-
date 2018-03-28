package config;

import java.util.Map;
import java.util.Set;

import translators.Translator;
import translators.TranslatorFacade;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface TranslateConfig extends CommonConfig {

    Set<TranslatorFacade.TRANSLATORS> getAllTranslations();

    boolean translationEnabled(String translator);

    boolean translationsEnabled();

    String getOutputDir();
}
