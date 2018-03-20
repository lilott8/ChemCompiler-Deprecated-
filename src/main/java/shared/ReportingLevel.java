package shared;

/**
 * @created: 2/15/18
 * @since: 0.1
 * @project: ChemicalCompiler
 *
 * This manages the level of reporting
 * Defined by the user for inference.
 * The user can chose to ignore all shared.errors,
 * All warnings, or all the things.
 */
public enum ReportingLevel {
    ERROR(100), WARNING(10), NONE(0);

    private int level;

    ReportingLevel(int value) {
        this.level = value;
    }

    public boolean warn() {
        return this.level == WARNING.level || this.level == NONE.level;
    }

    public boolean error() {
        return this.level == ERROR.level;
    }

    public boolean disabled() {
        return this.level == NONE.level;
    }

}
