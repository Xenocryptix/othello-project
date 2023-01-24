package Othello.model;

/**
 * Represents a disk in the Othello game. There three possible values:
 * Disk.Black, Disk.WHITE and Disk.EMPTY.
 */
public enum Disk {
    BLACK, WHITE, EMPTY;

    /**
     * Returns the other disk.
     *
     * @return the other disk is this disk is not EMPTY or EMPTY
     */
    //@ ensures this == BLACK ==> \result == WHITE && this == WHITE ==> \result == BLACK && this == EMPTY ==> \result == EMPTY;
    public Disk other() {
        if (this == BLACK) {
            return WHITE;
        } else if (this == WHITE) {
            return BLACK;
        } else {
            return EMPTY;
        }
    }
}
