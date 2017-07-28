package Shared;

/**
 * @created: 7/28/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class Tuple<L, R> {

    R right;
    L left;

    public Tuple(L left, R right) {
        this.right = right;
        this.left = left;
    }

    public R getRight() {
        return right;
    }

    public L getLeft() {
        return left;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Left: ").append(left.toString()).append("\t\t").append("Right: ").append(right.toString());
        return sb.toString();
    }
}
