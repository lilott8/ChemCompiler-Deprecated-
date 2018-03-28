package translators.microdrop.plugin;

import com.google.gson.annotations.SerializedName;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class UserPrompt {

    @SerializedName("message")
    String message = "";
    @SerializedName("schema")
    String schema = "";

    public UserPrompt() {
    }

    public UserPrompt(String message, String schema) {
        this.message = message;
        this.schema = schema;
    }
}
