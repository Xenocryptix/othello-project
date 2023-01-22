package Othello;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Random;


public class OthelloGame implements Game {
    private final Board board;
    private Player player1;
    private Player player2;
    private List<Move> validMoves;
    //predefined directional array
    private final int[][] dxy = {
        {0, 1}, {1,  0}, {0,  -1}, {-1, 0},
        {1, 1}, {1, -1}, {-1, -1}, {-1, 1}
    };
    private int[][] checked = new int[10][10];
    private int turn;

    public OthelloGame() {
        this.board = new Board();
        this.player1 = null;
        this.player2 = null;
        turn = 0;
        validMoves = getValidMoves();
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
     * Return turn counter
     *
     * @return turn
     */
    /*@
    ensures \result >= 0;
    pure
    */
    public int getCounter() {
        return turn;
    }

    /**
     * Check if the game is over, i.e., there is a winner or no more moves are available.
     *
     * @return whether the game is over
     */
    /*@
    ensures board.gameOver() ==>  \result == true || validMoves.isEmpty() ==> \result == true;
    pure;
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
    /*@
    pure;
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
    /*@
    ensures board.countDisk(Disk.BLACK) > board.countDisk(Disk.WHITE) ==> \result == player1;
    ensures board.countDisk(Disk.WHITE) > board.countDisk(Disk.BLACK) ==> \result == player2;
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
     * (could go unused)
     * @param row, col
     * @return true false
     */
    public boolean hasNearby(int row, int col) {
        for (int[] dir: dxy) {
            int dRow = row + dir[0];
            int dCol = col + dir[1];
            if (!board.isField(dRow, dCol))
                continue;
            if (!board.isEmptyField(dRow, dCol))
                return true;
        }
        return false;
    }

    /**
     * Check if a move is a valid move
     *
     * @param move the move to check
     * @return true if the move is a valid move
     */
    @Override
    public boolean isValidMove(Move move) {
        int row = ((OthelloMove) move).getRow();
        int col = ((OthelloMove) move).getCol();
        Disk disk = ((OthelloMove) move).getDisk();
        for (Move current : validMoves) {
            int cRow = ((OthelloMove) current).getRow();
            int cCol = ((OthelloMove) current).getCol();
            Disk cDisk = ((OthelloMove) current).getDisk();
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
            //Starting point of a chosen direction
            int dRow = row + dir[0];
            int dCol = col + dir[1];
            //Traverse in that direction until meeting the disk with same color
            while (board.isField(dRow, dCol)) {
                if (board.getField(dRow, dCol).equals(disk)) {
                    break;
                }
                dRow += dir[0];
                dCol += dir[1];
            }
            if (board.isField(dRow, dCol)) {
                if (board.getField(dRow, dCol).equals(disk) &&
                   ((dRow == row && Math.abs(dCol - col) > 1) ||
                    (dCol == col && Math.abs(dRow - row) > 1) ||
                    (Math.abs(dCol - col) > 1 && Math.abs(dRow - row) > 1))) {
                    Move move = new OthelloMove(disk, row, col);
                    if (!isValidMove(move)) {
                        validMoves.add(new OthelloMove(disk, row, col));
                        break;
                    }
                }
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
        validMoves = new ArrayList<>();
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                if (!board.isEmptyField(i, j)) {
                    for (int[] dir: dxy) {
                        int row = i + dir[0];
                        int col = j + dir[1];
                        if (board.isEmptyField(row, col))
                            checkDirection(row, col, board.getField(i, j).other());
                    }
                }
            }
        }
        return validMoves;
    }
    public Move getRandomValidMove(Disk disk) {
        List<Move> currentMovesForDisk = new ArrayList<>();
        for (Move move : validMoves) {
            if (((OthelloMove) move).getDisk().equals(disk)) {
                currentMovesForDisk.add(move);
            }
        }
        return currentMovesForDisk.get(new Random().nextInt(currentMovesForDisk.size()));
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
            turn++;
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
     * @param newBoard the 2D array
     */
    public void setBoard(Disk[][] newBoard) {
        board.setBoard(newBoard);
        getValidMoves();
    }
}
