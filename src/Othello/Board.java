package Othello;

public class Board {
    /*@
        public invariant ((\forall int row; row >= 0 && row < DIM;
                          (\forall int col; col >= 0 && col < DIM;
                            fields[row][col] == Disk.WHITE || fields[row][col] == Disk.BLACK || fields[row][col] == Disk.EMPTY)));
    */
    /**
     * Dimension of the board, i.e., if set to 8, the board has 8 rows and 8 columns.
     */
    public static final int DIM = 8;
    private static final String LINE = "  ---+---+---+---+---+---+---+---";
    private /*@spec_public */ Disk[][] fields;

    /**
     * Creates an empty board.
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM); ((\forall int j;j <DIM && j >= 0 ;fields[i][j] == Disk.EMPTY)));
    //TODO: EDIT THE JML SO IT CHECKS THE ONES FOR THE MIDDLE
    public Board() {
        fields = new Disk[DIM][DIM];
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                fields[i][j] = Disk.EMPTY;  // Initialize the cell
            }
        }
        fields[3][3] = Disk.WHITE;
        fields[3][4] = Disk.BLACK;
        fields[4][3] = Disk.BLACK;
        fields[4][4] = Disk.WHITE;
    }

    /**
     * Creates a deep copy of this field.
     */
    /*@
        ensures \result != this;
        ensures (\forall int i; (i >= 0 && i < DIM); ((\forall int j; j < DIM && j >= 0; \result.fields[i] == this.fields[i]))) ;
    */
    public Board deepCopy() {
        Disk[][] copy = new Disk[DIM][DIM];
        Board board = new Board();
        copy = this.fields.clone();
        board.fields = copy;
        return board;
    }

    /**
     * Calculates the index in the linear array of fields from a (row, col)
     * pair.
     *
     * @return the index belonging to the (row,col)-field
     */
    /*@
        requires row >= 0 && row < DIM;
        requires col >= 0 && row < DIM;
    */
    public int index(int row, int col) {
        return row * DIM + col;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     *
     * @return true if 0 <= index < DIM*DIM
     */
    //@ ensures index >= 0 && index < DIM*DIM ==> \result == true;
    //@ pure;
    public boolean isField(int index) {
        return index >= 0 && index < DIM * DIM;
    }

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
    /*@
        requires isField(row, col);
        ensures \result == Disk.EMPTY || \result == Disk.BLACK || \result == Disk.WHITE;
        pure;
    */
    public Disk getField(int row, int col) {
        return fields[row][col];
    }

    /**
     * Returns the content of the field i.
     *
     * @param i the number of the field
     * @return the mark on the field
     */
    /*@
        requires isField(i);
        ensures \result == Disk.EMPTY || \result == Disk.BLACK || \result == Disk.WHITE;
        pure;
    */
    public Disk getField(int i) {
        int row = getRow(i);
        int column = getColumn(i);
        return fields[row][column];
    }

    /**
     * Returns the column from a given index
     *
     * @param i the index
     * @return the column
     */
    //@pure
    public int getColumn(int i) {
        return i % DIM;
    }

    /**
     * Returns the column from a given index
     *
     * @param i the index
     * @return the column
     */
    //@pure
    public int getRow(int i) {
        return i / DIM;
    }

    /**
     * Returns true if the field referred to by the (row,col) pair it empty.
     *
     * @param row the row of the field
     * @param col the column of the field
     * @return true if the field is empty
     */
    /*@
        requires isField(row, col);
        ensures getField(row, col) == Disk.EMPTY ==> \result == true;
        pure
    */
    public boolean isEmptyField(int row, int col) {
        return getField(row, col) == Disk.EMPTY;
    }

    /**
     * Tests if the whole board is full.
     *
     * @return true if all fields are occupied
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM); (\forall int j;j >= 0 && j < DIM ;fields[i][j] == Disk.WHITE || fields[i][j] == Disk.BLACK ));
    //@ pure
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

    /**
     * Counts the number of times a certain disk is on the board
     *
     * @param disk the disk to be counted
     * @return the number of times that disk is on the board
     */
    /*@
        requires disk != null;
        ensures \result > 0;
        pure
    */
    public int countDisk(Disk disk) {
        int count = 0;
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                if (fields[row][col].equals(disk)) {
                    count++;
                }
            }
        }
        return count;
    }

    /**
     * Checks if the disk d has won. A disk wins if it has more
     * disk in the board, and when the board is full.
     *
     * @param d the disk in question
     * @return true if the disk has won
     */
    //@ ensures isFull();
    //@ pure
    public boolean isWinner(Disk d) {
        return isFull() && (countDisk(d) > countDisk(d.other()));
    }

    /**
     * Returns true if the game has a winner. This is the case when the
     * board is full and either of the colors has greater number of disks.
     *
     * @return true if the student has a winner.
     */
    //@ ensures isWinner(Disk.WHITE) || isWinner(Disk.BLACK) ==> \result == true;
    //@ pure
    public boolean hasWinner() {
        return isWinner(Disk.WHITE) || isWinner(Disk.BLACK);
    }

    /**
     * Sets the content of the field represented by
     * the (row,col) pair to the mark m.
     *
     * @param row  the field's row
     * @param col  the field's column
     * @param disk the mark to be placed
     */
    /*@
        requires isField(row, col);
        ensures getField(row, col) == disk;
    */
    public void setField(int row, int col, Disk disk) {
        fields[row][col] = disk;
    }

    /**
     * Sets the content of field i to the Disk disk.
     *
     * @param i    the field number
     * @param disk the mark to be placed
     */
    /*@
        requires isField(i);
        ensures getField(i) == disk;
    */
    public void setField(int i, Disk disk) {
        int row = getRow(i);
        int col = getColumn(i);
        fields[row][col] = disk;
    }
    /**
     * Empties all fields of this board excepts the disks in the middle.
     */
    //@
    //TODO: JML HEREEEEEE
    public void reset() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                if (i != 3 && j != 3 && i != 4 && j != 4){
                    fields[i][j] = Disk.EMPTY;
                }
            }
        }
    }

    /**
     * Flip a cell
     *
     * @param i index
     */
    public void flip(int i) {
        int row = getRow(i);
        int col = getColumn(i);
        if (isEmptyField(row, col)) {
            Disk disk = getField(row, col);
            setField(row, col, disk.other());
        }
    }

    /**
     * Flip a cell
     *
     * @param row, col
     */
    public void flip(int row, int col) {
        if (isEmptyField(row, col)) {
            Disk disk = getField(row, col);
            setField(row, col, disk.other());
        }
    }

    /**
     * Set the whole current board
     * @param board the 2D array
     */
    public void setBoard(Disk[][] board) {
        this.fields = board;
    }

    @Override
    public String toString() {
        String s = "   A   B   C   D   E   F   G   H\n";
        for (int i = 0; i < DIM; i++) {
            String row = Integer.toString(i + 1) + " ";
            for (int j = 0; j < DIM; j++) {
                row += " " + getField(i, j).toString().substring(0, 1).replace("E", " ") + " ";
                if (j < DIM - 1) {
                    row = row + "|";
                }
            }
            s = s + row;
            if (i < DIM - 1) {
                s = s + "\n" + LINE + "\n";
            }
        }
        return s;
    }
}
