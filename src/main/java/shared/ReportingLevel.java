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

    ReportingLevel(int value) {
        this.level = level;
    }

    private int level;

    public boolean warn() {
        return level == WARNING.level || level == NONE.level;
    }

    public boolean error() {
        return level == ERROR.level;
    }

    public boolean disabled() {
        return level == NONE.level;
    }

}
