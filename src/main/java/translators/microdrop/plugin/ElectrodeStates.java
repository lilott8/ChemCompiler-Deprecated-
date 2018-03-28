package translators.microdrop.plugin;

import com.google.gson.annotations.SerializedName;

import java.util.ArrayList;
import java.util.List;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ElectrodeStates {
    @SerializedName("index")
    List<String> electrodes = new ArrayList<>();
    @SerializedName("values")
    List<Boolean> electrodeStates = new ArrayList<>();
    @SerializedName("index_dtype")
    String indexDataType = "object";
    @SerializedName("dtype")
    String dataType;
    @SerializedName("type")
    String type = "Series";


}
