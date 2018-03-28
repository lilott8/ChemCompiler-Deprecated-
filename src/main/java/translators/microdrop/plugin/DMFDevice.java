package translators.microdrop.plugin;

import com.google.gson.annotations.SerializedName;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class DMFDevice {
    @SerializedName("electrode_states")
    ElectrodeStates electrodeStates;
}
