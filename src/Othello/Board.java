package Othello;

public class Board {
    /**
     * Dimension of the board, i.e., if set to 8, the board has 8 rows and 8 columns.
     */
    public static final int DIM = 8;
    private static final String DELIM = "     ";
    private Disk[][] fields;

    /**
     * Creates an empty board.
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM); ((\forall int j;j <DIM && j >= 0 ;fields[i][j] == Disk.EMPTY) )) ;
    public Board() {
        fields = new Disk[DIM][DIM];
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                fields[i][j] = Disk.EMPTY;  // Initialize the cell
            }
        }
    }

    /**
     * Creates a deep copy of this field.
     */
    /*@ ensures \result != this;
    @ ensures (\forall int i; (i >= 0 && i < DIM); ((\forall int j;j <DIM && j >= 0 ;\result.fields[i] == this.fields[i]) )) ;
     @*/
    public Board deepCopy() {
        Board board = new Board();
        fields = this.fields.clone();
        board.fields = fields;
        return board;
    }

    /**
     * Calculates the index in the linear array of fields from a (row, col)
     * pair.
     *
     * @return the index belonging to the (row,col)-field
     */
    /*@ requires row >= 0 && row < DIM;
    requires col >= 0 && row < DIM;
     @*/
    public int index(int row, int col) {
        return row * DIM + col;
    }
    //TODO: ask about the the methods containing the index

    /**
     * Returns true of the (row,col) pair refers to a valid field on the board.
     *
     * @return true if 0 <= row < DIM && 0 <= col < DIM
     */
    //@ ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
    //@pure;
    public boolean isField(int row, int col) {
        return row >= 0 && row < DIM && col >= 0 && col < DIM;
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     *
     * @param row the row of the field
     * @param col the column of the field
     * @return the disk on the field
     */
    /*@ requires isField(row, col);
    ensures \result == Disk.EMPTY || \result == Disk.BLACK || \result == Disk.WHITE;
     @*/
    public Disk getField(int row, int col) {
        return fields[row][col];
    }

    /**
     * Returns true if the field referred to by the (row,col) pair it empty.
     *
     * @param row the row of the field
     * @param col the column of the field
     * @return true if the field is empty
     */
    /*@ requires isField(row, col);
    ensures getField(row, col) == Disk.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int row, int col) {
        return getField(row, col) == Disk.EMPTY;
    }

    /**
     * Tests if the whole board is full.
     *
     * @return true if all fields are occupied
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM); (\forall int j;j >= 0 && j < DIM ;fields[i][j] == Disk.WHITE || fields[i][j] == Disk.BLACK ));
    public boolean isFull() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                if (fields[i][j].equals(Disk.EMPTY)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     *
     * @return true if the game is over
     */
    //@ ensures isFull() || hasWinner() ==> \result == true;
    public boolean gameOver() {
        return isFull() || hasWinner();
    }
    //TODO:Checking if there is a winner methods
}
