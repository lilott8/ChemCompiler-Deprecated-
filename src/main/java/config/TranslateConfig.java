package config;

import java.util.Set;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public interface TranslateConfig {

    Set<String> getAllTranslations();
    boolean translationEnabled(String translator);
    boolean translationsEnabled();
    String getOutputDir();
}
