package translators.microdrop;

import com.google.gson.Gson;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import compilation.datastructures.cfg.CFG;
import config.TranslateConfig;
import translators.Translator;
import translators.microdrop.plugin.PluginData;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class MicroDropTranslator implements Translator {

    public static final Logger logger = LogManager.getLogger(MicroDropTranslator.class);
    public static final String VERSION = "0.2.0";
    private MicroDrop drop;

    @Override
    public Translator setConfig(TranslateConfig config) {
        return this;
    }

    @Override
    public Translator runTranslation(CFG controlFlowGraph) {
        this.drop = new MicroDrop("default", new PluginData());

        return this;
    }

    @Override
    public void toFile(String output) {
        Gson gson = new Gson();
        String json = gson.toJson(this.drop);
        logger.warn(json);
    }

    @Override
    public void toFile() {

    }
}
