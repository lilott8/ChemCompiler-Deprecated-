package translators.microdrop.plugin;

import com.google.gson.annotations.SerializedName;

import java.util.ArrayList;
import java.util.List;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class DropRoutes {

    @SerializedName("index")
    private List<String> index = new ArrayList<>();
    @SerializedName("values")
    private List<String> values = new ArrayList<>();
    @SerializedName("index_dtype")
    private String indexType = "object";
    @SerializedName("columns")
    private List<String> columns = new ArrayList<>();
    @SerializedName("type")
    private String type = "DataFrame";

    public DropRoutes() {
        // this.columns.add("route_i");
        // this.columns.add("electrode_i");
        // this.columns.add("transition_i");
    }

    public DropRoutes(List<String> index, List<String> values, String indexType, List<String> columns, String type) {
        this.index.addAll(index);
        this.values.addAll(values);
        this.indexType = indexType;
        this.columns.addAll(columns);
        this.type = type;
    }
}
