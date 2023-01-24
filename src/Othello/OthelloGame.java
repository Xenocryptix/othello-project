package Othello;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Random;

/**
 * A class representing and othello game which implements and interface Game. The class handles
 * the full implementation of the game. It creates a new board for the game and adds two players
 * to the game. It also generates all valid moves for a game and has a method which allows making a move
 * for the game which flips all the tiles in the middle of the two disks. IT shows the state of the game
 * using a method and the board can be reset through OthelloGame and even set to a new array
 */
public class OthelloGame implements Game {
    private Board board;
    private Player player1;
    private Player player2;
    private List<Move> validMoves = new ArrayList<>(); //Valid move array list
    private List<Move> validBlack = new ArrayList<>(); //Valid move for black
    private List<Move> validWhite = new ArrayList<>(); //Valid move for white

    //Predefined directional array
    private final int[][] dxy = {
            {0, 1}, {1, 0}, {0, -1}, {-1, 0},
            {1, 1}, {1, -1}, {-1, -1}, {-1, 1}
    };
    private Disk current;
    private final Random RANDOM = new Random();

    /**
     * Creates a new othello game by initialising the board to a new board, two players and setting the first move to be a
     * black disc
     */
    public OthelloGame() {
        this.board = new Board();
        this.player1 = null;
        this.player2 = null;
        current = Disk.BLACK;
        getValidMoves();
    }

    /**
     * Sets player 1 to p1 passed as a parameter
     *
     * @param p1 Player 1 object
     */
    /*@
        requires p1 != null;
        ensures player1 == p1 ==> true;
    */
    public void setPlayer1(Player p1) {
        this.player1 = p1;
    }

    /**
     * Set player 2 to p2 passed as a parameter
     *
     * @param p2 Player 2 object
     */
    /*@
        requires p2 != null;
        ensures player2 == p2 ==> true;
    */
    public void setPlayer2(Player p2) {
        this.player2 = p2;
    }

    /**
     * Check if black disk ran out of moves
     *
     * @return True, if the game is over for black, otherwise false.
     */
    /*@
        ensures validBlack.isEmpty() ==> \result == true;
        pure;
    */
    public boolean currentPlayerOver() {
        if (current.equals(Disk.BLACK))
            return validBlack.isEmpty();
        else
            return validWhite.isEmpty();
    }


    /**
     * Check if the game is over, i.e., there are no more valid moves or the board is full.
     *
     * @return True, if the game is over, otherwise false.
     */
    /*@
        ensures validMoves.isEmpty() ==> \result == true;
        pure;
    */
    @Override
    public boolean isGameover() {
        getValidMoves();
        return board.isFull() || currentPlayerOver() ;
    }

    /**
     * Returns the disk that has the current turn
     *
     * @return Current disk
     */
    //@ ensures \result == Disk.BLACK || \result == Disk.WHITE;
    public Disk getCurrentDisk() {
        return current;
    }

    /**
     * Query whose turn it is
     *
     * @return The player whose turn it is
     */
    //@ ensures \result == player1 || \result == player2;
    //@ pure;
    @Override
    public Player getTurn() {
        if (current.equals(Disk.BLACK)) {
            return player1;
        } else {
            return player2;
        }
    }

    /**
     * Gets the winner of the game. If the game is a draw, then this null is returned.
     *
     * @return The player that won the game, or null if no player is the winner
     */
    /*@
        ensures board.countDisk(Disk.BLACK) > board.countDisk(Disk.WHITE) ==> \result == player1;
        ensures board.countDisk(Disk.WHITE) > board.countDisk(Disk.BLACK) ==> \result == player2;
        ensures board.countDisk(Disk.WHITE) == board.countDisk(Disk.BLACK) ==> \result == null;
        pure;
    */
    @Override
    public Player getWinner() {
        if (board.isWinner(Disk.BLACK)) {
            return player1;
        } else if (board.isWinner(Disk.WHITE)) {
            return player2;
        } else {
            return null;
        }
    }

    /**
     * Check if a move is a valid move
     *
     * @param move The move to check
     * @return True if the move is valid, otherwise false
     */
    /*@
    requires move != null;
    ensures \result == true ==> validMoves.contains(move);
    pure
    */
    @Override
    public boolean isValidMove(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk disk = ((OthelloMove) move).getDisk();
        for (Move curMove : validMoves) {
            int cRow = ((OthelloMove) curMove).getRow();
            int cCol = ((OthelloMove) curMove).getCol();
            Disk cDisk = ((OthelloMove) curMove).getDisk();
            if (cRow == row && cCol == col && Objects.equals(cDisk, disk)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks all 8 directions of a disc to find a move that could be valid.
     * A check is made to look at the neighboring tile in a certain direction that it is the other disc,
     * and it is not empty. If it passes that, then it moves another tile and checks it again until
     * an empty tile is found and then that tile is added to the valid moves list as a new valid move.
     *
     * @param row  row The row of the move to check valid moves for
     * @param col  col The column of the move to check valid moves for
     * @param disk disk The disk of the move to check valid moves for
     */
    //TODO:JML
    public void checkDirection(int row, int col, Disk disk) {
        for (int[] dir : dxy) {
            int nRow = row + dir[0];
            int nCol = col + dir[1];
            int count = 0;
            while (board.isField(nRow, nCol)) {
                if (board.getField(nRow, nCol).equals(disk))
                    break;
                if (board.getField(nRow, nCol).equals(Disk.EMPTY)) {
                    if (board.getField(nRow - dir[0], nCol - dir[1]).equals(disk.other()) && count > 0) {
                        Move move = new OthelloMove(disk, nRow, nCol);
                        if (!isValidMove(move)) {
                            validMoves.add(move);
                            if (disk.equals(Disk.WHITE))
                                validWhite.add(move);
                            else
                                validBlack.add(move);
                        }
                    }
                    break;
                }
                nRow += dir[0];
                nCol += dir[1];
                count++;
            }
        }
    }

    /**
     * Return all moves that are valid in the current state of the game by checking all directions
     * of all the tiles in the game that are not empty.
     *
     * @return the list of currently valid moves
     */
    /*@
        pure
    */
    //TODO:JML
    @Override
    public List<Move> getValidMoves() {
        validMoves.clear();
        validBlack.clear();
        validWhite.clear();
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                if (!board.isEmptyField(i, j)) {
                    Disk disk = board.getField(i, j);
                    checkDirection(i, j, disk);
                }
            }
        }
        return validMoves;
    }

    /**
     * Return valid moves for a specified color
     *
     * @param disk The disk color
     * @return move The move-list
     */
    public List<Move> getValidMoves(Disk disk) {
        getValidMoves();
        if (disk.equals(Disk.BLACK))
            return validBlack;
        else
            return validWhite;
    }


    /**
     * Return a random valid move for a specified disk
     *
     * @param disk The disk color which random move would be generated for
     * @return move The random move
     */
    /*@
        requires disk != Disk.EMPTY;
        ensures getValidMoves().contains(\result) && ((OthelloMove) \result).getDisk().equals(disk);
    */
    public Move getRandomValidMove(Disk disk) {
        List<Move> currentMoves = getValidMoves(disk);
        return currentMoves.get(RANDOM.nextInt(currentMoves.size()));
    }

    /**
     * Performing the gives move, unless this move is not a valid move which is done by going through
     * the tiles that are between the valid move given and another disk of the same color and switching
     * the other tiles between them to the color of the given move.
     *
     * @param move The move to play
     */
    /*@
        ensures validMoves != \old(validMoves);
        ensures current == \old(current.other());
    */
    //TODO: DON'T UNDERSTAND
    @Override
    public void doMove(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk disk = ((OthelloMove) move).getDisk();
        if (isValidMove(move)) {
            board.setField(row, col, disk);
            for (int[] dir : dxy) {
                int dRow = row + dir[0];
                int dCol = col + dir[1];
                while (board.isField(dRow, dCol)) {
                    if (board.getField(dRow, dCol).equals(disk)) {
                        break;
                    }
                    dRow += dir[0];
                    dCol += dir[1];
                }
                if (board.isField(dRow, dCol) && board.getField(dRow, dCol).equals(disk)) {
                    dRow -= dir[0];
                    dCol -= dir[1];
                    while (!board.getField(dRow, dCol).equals(disk)) {
                        board.flip(dRow, dCol);
                        dRow -= dir[0];
                        dCol -= dir[1];
                    }
                }
            }
            validMoves = getValidMoves();
            current = disk.other();
        }
    }

    /**
     * Return the current state of the board as a string
     * with a description of whose turn it is to play
     *
     * @return The board with the player's turn
     */
    public String toString() {
        return board + "\nIt's " + getTurn() + " turn\n";
    }

    /**
     * Return the board object
     *
     * @return board that is used in the game
     */
    /*@
        ensures (\forall int i; i >= 0 && i <= 63; \result.getField(i) == board.getField(i));
        pure
    */
    public Board getBoard() {
        return board;
    }

    /**
     * Sets the current board to a new board using a 2D array
     *
     * @param newBoard The new board as a 2D array to change the current board
     */
    /*@
        ensures (\forall int i; i >= 0 && i <= 7; (\forall int j;j >= 0 && j <= 7; newBoard[i][j] == board.getField(i,j)));
        ensures validMoves != \old(validMoves);
        pure
    */
    public void setBoard(Disk[][] newBoard) {
        board.setBoard(newBoard);
        getValidMoves();
    }

    /**
     * Sets the current board to a new board using a board object
     *
     * @param newBoard The new board as an object to change the current board
     */
    public void setBoard(Board newBoard) {
        this.board = newBoard;
        getValidMoves();
    }

    /**
     * Resets the current board to the initial board by initialising the board
     */
    //@ ensures validMoves != \old(validMoves);
    public void reset() {
        board.reset();
        getValidMoves();
    }
}
