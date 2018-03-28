package translators.microdrop.plugin;

import com.google.gson.annotations.SerializedName;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class StepLabel {

    @SerializedName("label")
    String label = "";

    public StepLabel() {
    }

    public StepLabel(String label) {
        this.label = label;
    }
}
