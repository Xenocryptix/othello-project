package Othello;

public class OthelloMove implements Move {
    private int row;
    private int col;
    private Disk disk;
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
