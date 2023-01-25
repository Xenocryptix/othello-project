package Othello.model;

import java.util.Arrays;

/**
 * Represents a board for an othello game. The board is initialised with the middle being white and black
 * The class can be used to set fields on the board and flip an already set field. It also checks for winners
 * inside the board and can reset it. Lastly, it has a toString for the presentation of the board.
 */
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
    private /*@ spec_public */ Disk[][] fields;
    //Predefined directional array
    protected static final int[][] DIRECTION_X_AND_Y = {
            {0, 1}, {1, 0}, {0, -1}, {-1, 0},
            {1, 1}, {1, -1}, {-1, -1}, {-1, 1}
    };

    /**
     * Creates an empty board.
     */
    /*@
        ensures (\forall int i; i >= 0 && i < DIM; (\forall int j; j >= 0 && j<= DIM; i != 3 && j != 3 && i != 4 && j != 4 ==> fields[i][j] == Disk.EMPTY));
        ensures fields[3][3] == Disk.WHITE && fields[3][4] == Disk.BLACK && fields[4][3] == Disk.BLACK && fields[4][4] == Disk.WHITE;
    */
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
        ensures (\forall int i; (i >= 0 && i < DIM); ((\forall int j; j < DIM && j >= 0; \result.fields[i][j] == this.fields[i][j]))) ;
    */
    public Board deepCopy() {
        Disk[][] copy = Arrays.copyOf(fields, fields.length);
        for (int i = 0; i < copy.length; i++) {
            copy[i] = Arrays.copyOf(fields[i], fields[i].length);
        }
        Board board = new Board();
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
        ensures \result >= 0 && \result < 64;
        pure
    */
    public int index(int row, int col) {
        return row * DIM + col;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     *
     * @return true if 0 <= index < DIM*DIM
     */
    /*@
        ensures index >= 0 && index < DIM*DIM ==> \result == true;
        pure;
    */
    public boolean isField(int index) {
        return index >= 0 && index < DIM * DIM;
    }

    /**
     * Returns true of the (row,col) pair refers to a valid field on the board.
     *
     * @return true if 0 <= row < DIM && 0 <= col < DIM
     */
    /*@
        ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
        pure;
    */
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
        pure
    */
    public Disk getField(int row, int col) {
        if (!isField(row, col))
            return null;
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
        pure
    */
    public Disk getField(int i) {
        int row = getRow(i);
        int column = getColumn(i);
        return getField(row, column);
    }

    /**
     * Returns the column from a given index
     *
     * @param i the index
     * @return the column
     */
    /*@
        requires isField(i);
        ensures \result >= 0 && \result < DIM;
        pure
    */
    public int getColumn(int i) {
        return i % DIM;
    }

    /**
     * Returns the row from a given index
     *
     * @param i the index
     * @return the row
     */
    /*@
        requires isField(i);
        ensures \result >= 0 && \result < DIM;
    */
    public int getRow(int i) {
        return i / DIM;
    }

    /**
     * Returns true if the field referred to by the (row,col) pair if empty.
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
    /*@
        ensures (\forall int i; i >= 0 && i < DIM; (\forall int j;j >= 0 && j < DIM ;fields[i][j] == Disk.WHITE || fields[i][j] == Disk.BLACK ));
        pure
    */
    public boolean isFull() {
        for (int index = 0; index < DIM * DIM; index++) {
            if (getField(index).equals(Disk.EMPTY)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Counts the number of times a certain disk is on the board
     *
     * @param disk the disk to be counted
     * @return the number of times that disk is on the board
     */
    /*@
        requires disk != null;
        ensures \result >= 0;
        pure
    */
    public int countDisk(Disk disk) {
        int count = 0;
        for (int index = 0; index < DIM * DIM; index++) {
            if (getField(index).equals(disk)) {
                count++;
            }
        }
        return count;
    }


    /**
     * Checks if a disk has won. A disk wins if it has more
     * disk in the board, and when the board is full.
     *
     * @param disk the disk in question
     * @return true if the disk has won
     */
    /*@
        requires disk == Disk.BLACK || disk == Disk.WHITE;
        ensures countDisk(disk) > countDisk(disk.other()) ==> true;
        pure
    */
    public boolean isWinner(Disk disk) {
        return countDisk(disk) > countDisk(disk.other());
    }

    /**
     * Returns true if the game has a winner. This is the case when the
     * board is full and either of the colors has greater number of disks.
     *
     * @return true if the board has a winner.
     */

    /*@
        ensures isWinner(Disk.WHITE) || isWinner(Disk.BLACK) ==> \result == true;
        pure
    */
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
     * Sets the content of field i to the specified disk.
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
     * Performing the gives move, unless this move is not a valid move which is done by going through
     * the tiles that are between the valid move given and another disk of the same color and switching
     * the other tiles between them to the color of the given move.
     *
     * @param move The move to play
     */
    /*@
        requires isField(((OthelloMove) move).getRow(), ((OthelloMove) move).getCol());
        requires ((OthelloMove) move).getDisk() == Disk.BLACK || ((OthelloMove) move).getDisk() == Disk.WHITE;
    */
    public void flipMove(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk disk = ((OthelloMove) move).getDisk();
        //First place the disk in the coordinate
        setField(row, col, disk);
        for (int[] dir: DIRECTION_X_AND_Y) {
            //We iterate in 8 direction, looking for flippable lines
            int directionRow = row + dir[0];
            int directionColumn = col + dir[1];
            int count = 0;
            while (isField(directionRow, directionColumn)) {
                //Continue to iterate in that direction while the tile is of opposite color
                if (getField(directionRow, directionColumn).equals(disk.other())) {
                    //Continue to move in that direction while counting the tiles that traversed
                    directionRow += dir[0];
                    directionColumn += dir[1];
                    count++;
                } else {
                    //Once we encountered another tile or empty tile, break out immediately
                    break;
                }
            }
            //We backtrack to the first tile, flipping all the disks in the middle
            if (isField(directionRow, directionColumn) && getField(directionRow, directionColumn).equals(disk)) {
                directionRow -= dir[0];
                directionColumn -= dir[1];
                for (int i = 0; i < count; i++) {
                    flip(directionRow, directionColumn);
                    directionRow -= dir[0];
                    directionColumn -= dir[1];
                }
            }
        }
    }

    /**
     * Empties all fields of this board excepts the disks in the middle.
     */
    /*@
        ensures (\forall int i; i >= 0 && i < DIM; (\forall int j; j >= 0 && j<= DIM; i != 3 && j != 3 && i != 4 && j != 4 ==> fields[i][j] == Disk.EMPTY));
        ensures fields[3][3] == Disk.WHITE && fields[3][4] == Disk.BLACK && fields[4][3] == Disk.BLACK && fields[4][4] == Disk.WHITE;
    */
    public void reset() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                fields[i][j] = Disk.EMPTY;
            }
        }
        fields[3][3] = Disk.WHITE;
        fields[3][4] = Disk.BLACK;
        fields[4][3] = Disk.BLACK;
        fields[4][4] = Disk.WHITE;
    }

    /**
     * Flip a cell using the index given
     *
     * @param i index of the field to be flipped
     */
    /*@
        requires isField(i);
        ensures getField(i) == \old(getField(i)).other();
        ensures countDisk(getField(i)) == \old(countDisk(getField(i)))+1;
    */
    public void flip(int i) {
        int row = getRow(i);
        int col = getColumn(i);
        if (!isEmptyField(row, col)) {
            Disk disk = getField(row, col);
            setField(row, col, disk.other());
        }
    }

    /**
     * Flip a cell using row and column
     *
     * @param row the row of the cell to be flipped
     * @param col the column of the cell to be flipped
     */
    /*@
        requires isField(row,col);
        ensures getField(row,col) == \old(getField(row,col)).other();
        ensures countDisk(getField(row,col)) == \old(countDisk(getField(row,col)))+1;
    */
    public void flip(int row, int col) {
        if (!isEmptyField(row, col)) {
            Disk disk = getField(row, col);
            setField(row, col, disk.other());
        }
    }

    /**
     * Return the board as a viewable string to print out in the UI
     *
     * @return s The string containing the board for UI
     */
    @Override
    public String toString() {
        String s = "   A   B   C   D   E   F   G   H\n";
        for (int i = 0; i < DIM; i++) {
            String row = Integer.toString(i+1) + " ";
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
