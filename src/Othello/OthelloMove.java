package Othello;

/**
 * Class that is responsible for representing an othello move, it stores the row, column and the disk of the move
 */
public class OthelloMove implements Move {
    private final int row;
    private final int col;
    private final Disk disk;
    public OthelloMove(Disk disk, int row, int col) {
        this.col = col;
        this.row = row;
        this.disk = disk;
    }

    /**
     * @return a column
     */
    //@ ensures \result == this.col;
    public int getCol() {
        return col;
    }

    /**
     * @return a row
     */
    //@ ensures \result == this.row;
    public int getRow() {
        return row;
    }

    /**
     * @return mark value
     */
    //@ ensures \result == this.disk;
    public Disk getDisk() {
        return disk;
    }
}
