package Othello.model;

import Othello.model.Disk;
import Othello.model.Move;

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
     * Returns the column of the current move
     *
     * @return a column
     */
    /*@
    ensures \result == this.col;
    pure
    */
    public int getCol() {
        return col;
    }

    /**
     * Returns the row of the current move
     *
     * @return a row
     */
    /*@
    ensures \result == this.row;
    pure
    */
    public int getRow() {
        return row;
    }

    /**
     * Returns the disk of the current mark which is either Black, White or Empty
     *
     * @return mark value
     */
    /*@
    ensures \result == this.disk;
    pure
    */
    public Disk getDisk() {
        return disk;
    }
}
