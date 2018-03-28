package translators.microdrop;

import com.google.gson.annotations.SerializedName;

import translators.microdrop.plugin.DMFDevice;
import translators.microdrop.plugin.DropBot;
import translators.microdrop.plugin.DropletPlanning;
import translators.microdrop.plugin.MicroDropElectrode;
import translators.microdrop.plugin.StepLabel;
import translators.microdrop.plugin.UserPrompt;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Step {

    @SerializedName("user_prompt_plugin")
    private UserPrompt userPrompt;
    @SerializedName("droplet_planning_plugin")
    private DropletPlanning dropletPlanning;
    @SerializedName("microdrop.electrode_controller_plugin")
    private MicroDropElectrode electrode;
    @SerializedName("step_label_plugin")
    private StepLabel stepLabel;
    @SerializedName("dropbot_plugin")
    private DropBot dropBot;
    @SerializedName("dmf_device_ui_plugin")
    private DMFDevice device;


}
