package Othello;

import java.util.ArrayList;
import java.util.List;

public class OthelloGame implements Game {
    private Board board;
    private Player player1;
    private Player player2;
    private List<Move> validMoves = new ArrayList<>();
    private int turn;

    public OthelloGame() {
        this.board = new Board();
        this.player1 = null;
        this.player2 = null;
        turn = 0;
        validMoves = getValidMoves();
    }

    /**
     * Set player 1
     *
     * @param p1 Player 1 object
     */
    public void setPlayer1(Player p1) {
        this.player1 = p1;
    }

    /**
     * Set player 2
     *
     * @param p2 Player 2 object
     */
    public void setPlayer2(Player p2) {
        this.player2 = p2;
    }

    /**
     * Return turn counter
     *
     * @return turn
     */
    public int getCounter() {
        return turn;
    }

    /**
     * Check if the game is over, i.e., there is a winner or no more moves are available.
     *
     * @return whether the game is over
     */
    @Override
    public boolean isGameover() {
        return board.gameOver() || validMoves.isEmpty();
    }

    /**
     * Query whose turn it is
     *
     * @return the player whose turn it is
     */
    @Override
    public Player getTurn() {
        //Depends if we default player1 go first
        if (turn % 2 == 0) {
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
    @Override
    public Player getWinner() {
        if (board.isWinner(Disk.WHITE)) {
            return player1;
        } else if (board.isWinner(Disk.BLACK)) {
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
    @Override
    public boolean isValidMove(Move move) {
        return validMoves.contains(move);
    }

    /**
     * Return all moves that are valid in the current state of the game
     *
     * @return the list of currently valid moves
     */
    @Override
    public List<Move> getValidMoves() {
        validMoves = new ArrayList<>();
        //TODO
        return null;
    }

    public boolean checkNE(Disk disk, int row, int col) {
        Disk otherDisk = disk.other();
        int i = row + 1;
        int j = col + 1;
        if (board.getField(row - 1, col - 1).equals(Disk.EMPTY)) {
            while (i < Board.DIM && j < Board.DIM) {
                if (board.getField(row, col).equals(otherDisk)) {
                    return true;
                }
                i = i + 1;
                j = j + 1;
            }
        }
        return false;
    }
    public boolean checkSE(Disk disk, int row, int col) {
        Disk otherDisk = disk.other();
        int i = row - 1;
        int j = col + 1;
        if (board.getField(row + 1, col - 1).equals(Disk.EMPTY)) {
            while (i >= 0 && j < Board.DIM) {
                if (board.getField(row, col).equals(otherDisk)) {
                    return true;
                }
                i = i - 1;
                j = j + 1;
            }
        }
        return false;
    }
    public boolean checkSW(Disk disk, int row, int col) {
        Disk otherDisk = disk.other();
        int i = row - 1;
        int j = col - 1;
        if (board.getField(row + 1, col + 1).equals(Disk.EMPTY)) {
            while (i >= 0 && j >= 0) {
                if (board.getField(row, col).equals(otherDisk)) {
                    return true;
                }
                i = i - 1;
                j = j - 1;
            }
        }
        return false;
    }
    public boolean checkNW(Disk disk, int row, int col) {
        Disk otherDisk = disk.other();
        int i = row + 1;
        int j = col - 1;
        if (board.getField(row - 1, col + 1).equals(Disk.EMPTY)) {
            while (i < Board.DIM && j >= 0) {
                if (board.getField(row, col).equals(otherDisk)) {
                    return true;
                }
                i = i + 1;
                j = j - 1;
            }
        }
        return false;
    }

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param move the move to play
     */
    @Override
    public void doMove(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk disk = ((OthelloMove) move).getDisk();
        validMoves = getValidMoves();
        if (isValidMove(move)) {
            board.setField(row, col, disk);
        }
        turn++;
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
}
