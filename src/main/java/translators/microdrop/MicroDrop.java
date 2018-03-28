package translators.microdrop;

import com.google.gson.annotations.SerializedName;

import java.util.ArrayList;
import java.util.List;

import translators.microdrop.plugin.PluginData;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class MicroDrop {

    @SerializedName("version")
    private String version = MicroDropTranslator.VERSION;
    @SerializedName("steps")
    private List<Step> steps = new ArrayList<>();
    @SerializedName("name")
    private String name;
    @SerializedName("plugin_data")
    private PluginData pluginData = null;

    public MicroDrop(String name, PluginData pluginData) {
        this.name = name;
        this.pluginData = pluginData;
    }

    public MicroDrop addStep(Step step) {
        this.steps.add(step);
        return this;
    }
}
