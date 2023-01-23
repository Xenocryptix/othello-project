package Othello;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Random;

/**
 * Represent a game for Othello
 */
public class OthelloGame implements Game {
    private final Board board;
    private Player player1;
    private Player player2;
    private List<Move> validMoves = new ArrayList<>(); //Valid move array list

    //Predefined directional array
    private final int[][] dxy = {
        {0, 1}, {1,  0}, {0,  -1}, {-1, 0},
        {1, 1}, {1, -1}, {-1, -1}, {-1, 1}
    };
    private Disk current;
    private Random rand = new Random();

    public OthelloGame() {
        this.board = new Board();
        this.player1 = null;
        this.player2 = null;
        current = Disk.BLACK;
        getValidMoves();
    }

    /**
     * Set player 1 to p1
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
     * Set player 2 to p2
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
     * Check if the game is over, i.e., there is a winner or no more moves are available.
     *
     * @return whether the game is over
     */
    /*@
        ensures validMoves.isEmpty() ==> \result == true;
        pure;
    */
    @Override
    public boolean isGameover() {
        getValidMoves();
        return board.isFull() || validMoves.isEmpty();
    }

    /**
     * Return current disk
     * @return disk current
     */
    //@ ensures \result == Disk.BLACK || \result == Disk.WHITE;
    public Disk getCurrentDisk() {
        return current;
    }

    /**
     * Query whose turn it is
     *
     * @return the player whose turn it is
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
     * Get the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the winner, or null if no player is the winner
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
     * @param move the move to check
     * @return true if the move is a valid move
     */
    //@ ensures \result == true || \result == false;
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
     * Much more convenient check (experimental)
     *
     * @param row row
     * @param col col
     * @param disk disk
     */
    public void checkDirection(int row, int col, Disk disk) {
        for (int[] dir: dxy) {
            int nRow = row + dir[0];
            int nCol = col + dir[1];
            int count = 0;
            while (board.isField(nRow, nCol)) {
                if (board.getField(nRow, nCol).equals(disk))
                    break;
                if (board.getField(nRow, nCol).equals(Disk.EMPTY)) {
                    if (board.getField(nRow - dir[0], nCol - dir[1]).equals(disk.other()) && count > 0){
                        Move move = new OthelloMove(disk, nRow, nCol);
                        if (!isValidMove(move)) {
                            validMoves.add(move);
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
     * Return all moves that are valid in the current state of the game
     *
     * @return the list of currently valid moves
     */
    @Override
    public List<Move> getValidMoves() {
        validMoves.clear();
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
     * Return a random valid move for a specified disk
     *
     * @param disk the disk color
     * @return move
     */
    public Move getRandomValidMove(Disk disk) {
        List<Move> currentMovesForDisk = new ArrayList<>();
        for (Move move : validMoves) {
            if (((OthelloMove) move).getDisk().equals(disk)) {
                currentMovesForDisk.add(move);
            }
        }
        return currentMovesForDisk.get(rand.nextInt(currentMovesForDisk.size()));
    }

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param move the move to play
     */
    //@ ensures validMoves != \old(validMoves);
    //@ ensures current == \old(current.other());
    @Override
    public void doMove(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk disk = ((OthelloMove) move).getDisk();
        if (isValidMove(move)) {
            board.setField(row, col, disk);
            for (int[] dir: dxy) {
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
     * Return the board as a string
     *
     * @return string
     */
    public String toString() {
        return board + "\nIt's " + getTurn() + " turn\n";
    }

    /**
     * Return the board object
     *
     * @return board
     */
    public Board getBoard() {
        return board;
    }

    /**
     * Set the whole current board
     *
     */
    //@ ensures validMoves != \old(validMoves);
    public void setBoard(Disk[][] newBoard) {
        board.setBoard(newBoard);
        getValidMoves();
    }

    /**
     * Reset current board
     *
     */
    //@ ensures validMoves != \old(validMoves);
    public void reset() {
        board.reset();
        getValidMoves();
    }
}
