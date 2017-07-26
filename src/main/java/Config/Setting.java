package Config;

/**
 * @created: 7/26/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Setting<T> {

    public final T setting;

    public Setting(T setting) {
        this.setting = setting;
    }

    public String toString() {
        return this.setting.toString();
    }
}
