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
     * Check if a tile is placeable using the upward direction
     *
     * @return move (if valid)
     */
    public boolean checkUp(Move move) {
        int row = ((OthelloMove) move).getRow() + 1;
        Disk disk = ((OthelloMove) move).getDisk().other();
        for (int i = row + 1; i < Board.DIM; i++) {
            if (board.getField(row, i).equals(disk)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Check if a tile is placeable using the downward direction
     *
     * @return move (if valid)
     */
    public boolean checkDown(Move move) {
        int row = ((OthelloMove) move).getRow() - 1;
        Disk disk = ((OthelloMove) move).getDisk().other();
        for (int i = row - 1; i >= 0; i--) {
            if (board.getField(row, i).equals(disk)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Check if a tile is placeable using the left direction
     *
     * @return move (if valid)
     */
    public boolean checkLeft(Move move) {
        int col = ((OthelloMove) move).getCol() - 1;
        Disk disk = ((OthelloMove) move).getDisk().other();
        for (int i = col - 1; i >= 0; i--) {
            if (board.getField(i, col).equals(disk)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Check if a tile is placeable using the right direction
     *
     * @return move (if valid)
     */
    public boolean checkRight(Move move) {
        int col = ((OthelloMove) move).getCol() + 1;
        Disk disk = ((OthelloMove) move).getDisk().other();
        for (int i = col + 1; i < Board.DIM; i++) {
            if (board.getField(i, col).equals(disk)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Check if a tile is placeable using the northeast direction
     *
     * @return move (if valid)
     */
    public boolean checkNE(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk otherDisk = ((OthelloMove) move).getDisk().other();
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

    /**
     * Check if a tile is placeable using the southeast direction
     *
     * @return move (if valid)
     */
    public boolean checkSE(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk otherDisk = ((OthelloMove) move).getDisk().other();
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

    /**
     * Check if a tile is placeable using the southwest direction
     *
     * @return move (if valid)
     */
    public boolean checkSW(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk otherDisk = ((OthelloMove) move).getDisk().other();
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

    /**
     * Check if a tile is placeable using the northwest direction
     *
     * @return move (if valid)
     */
    public boolean checkNW(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk otherDisk = ((OthelloMove) move).getDisk().other();
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
     * Return all moves that are valid in the current state of the game
     *
     * @return the list of currently valid moves
     */
    @Override
    public List<Move> getValidMoves() {
        validMoves = new ArrayList<>();
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                if (!board.isEmptyField(i, j)) {
                    Move move = new OthelloMove(board.getField(i, j), i, j);
                    if (checkUp(move) || checkDown(move) || checkLeft(move) || checkRight(move) ||
                        checkNE(move) || checkSE(move)   || checkSW(move)   || checkNW(move)  ) {
                        validMoves.add(move);
                    }
                }
            }
        }
        return validMoves;
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
