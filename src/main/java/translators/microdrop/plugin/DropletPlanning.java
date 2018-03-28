package translators.microdrop.plugin;

import com.google.gson.annotations.SerializedName;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class DropletPlanning {

    @SerializedName("transition_duration_ms")
    int transitionDurationMS = 750;
    @SerializedName("route_repeats")
    int routeRepeats = 1;
    @SerializedName("repeat_duration_s")
    int repeatDuration = 0;
    @SerializedName("trail_length")
    int trailLength = 1;
    @SerializedName("drop_routes")
    DropRoutes routes;

    public DropletPlanning() {
    }

    public DropletPlanning(int transitionDurationMS, int routeRepeats, int repeatDuration, int trailLength) {
        this.transitionDurationMS = transitionDurationMS;
        this.routeRepeats = routeRepeats;
        this.repeatDuration = repeatDuration;
        this.trailLength = trailLength;
    }
}
