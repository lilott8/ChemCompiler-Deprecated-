package translators.microdrop.plugin;

import com.google.gson.annotations.SerializedName;

/**
 * @created: 3/28/18
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class DropBot {

    @SerializedName("duration")
    private int duration = 1000;
    @SerializedName("frequency")
    private int frequency = 10000;
    @SerializedName("max_repeats")
    private int maxRepeats = 3;
    @SerializedName("voltage")
    private float voltage = 80;
    @SerializedName("volume_threshold")
    private int volumeThreshold = 0;

    public DropBot() {
    }

    public DropBot(int duration, int frequency, int maxRepeats, float voltage, int volumeThreshold) {
        this.duration = duration;
        this.frequency = frequency;
        this.maxRepeats = maxRepeats;
        this.voltage = voltage;
        this.volumeThreshold = volumeThreshold;
    }
}
