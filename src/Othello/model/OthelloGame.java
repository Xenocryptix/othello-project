package Othello.model;

import Othello.players.AbstractPlayer;
import Othello.players.Player;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * A class representing and othello game which implements and interface Game. The class handles
 * the full implementation of the game. It creates a new board for the game and adds two players
 * to the game. It also generates all valid moves for a game and has a method which allows making a move
 * for the game which flips all the tiles in the middle of the two disks. IT shows the state of the game
 * using a method and the board can be reset through OthelloGame and even set to a new array
 */
public class OthelloGame implements Game {
    /*@
     public invariant !isGameover() ==> getValidMoves().size() > 0;
     public invariant !isGameover() ==> getWinner() == null;
     public invariant !isGameover() ==> getTurn() != null;
    */

    //Predefined directional array
    private final int[][] dxy = {
            {0, 1}, {1, 0}, {0, -1}, {-1, 0},
            {1, 1}, {1, -1}, {-1, -1}, {-1, 1}
    };
    private final List<Move> validBlack = new ArrayList<>(); //Valid move for black
    private final List<Move> validWhite = new ArrayList<>(); //Valid move for white
    private Board board;
    private Player player1;
    private Player player2;
    private List<Move> validMoves = new ArrayList<>(); //Valid move array list
    private Disk current;

    /**
     * Creates a new Othello game by initialising the board to a new board, two players and
     * setting the first move to be a black disc
     */
    /*@
        ensures current == Disk.BLACK;
        ensures player1 == null;
        ensures player2 == null;
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
        return board.isFull() || validMoves.isEmpty();
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
    /*@
        ensures \result == player1 || \result == player2;
        pure;
    */
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
        ensures board.countDisk(Disk.BLACK) >  board.countDisk(Disk.WHITE) ==> \result == player1;
        ensures board.countDisk(Disk.WHITE) >  board.countDisk(Disk.BLACK) ==> \result == player2;
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
     * Check if a move is a valid move, by checking whether the move exists in the valid moves list
     * Could've been 1 line if contains() works
     *
     * @param move The move to check
     * @return True if the move is valid, otherwise false
     */
    /*@
        requires move != null;
        ensures \result == true ==> validMoves.contains(move);
        pure;
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
     * The check looks for lines in all 8 direction, seeing if there's a full and uninterrupted line of opposite
     * color with an empty tile as the endpoint. This endpoint would be a possible coordinate to place in the
     * tile with the same color as the starting point
     *
     * @param row  The row of the move to check valid moves for
     * @param col  The column of the move to check valid moves for
     * @param disk The disk of the move to check valid moves for
     */
    //@ requires board.isField(row, col);
    public void checkDirection(int row, int col, Disk disk) {
        //Traverse from 8 direction from a specified tile
        for (int[] dir : dxy) {
            int nRow = row + dir[0];
            int nCol = col + dir[1];
            int count = 0;
            //Iterate in the chosen direction
            while (board.isField(nRow, nCol)) {
                if (board.getField(nRow, nCol).equals(disk))
                    //If a tile with the same color as the starting point is encountered, break immediately
                    break;
                if (board.getField(nRow, nCol).equals(Disk.EMPTY)) {
                    /*
                        If a tile is empty, there could be 2 possible cases:
                        There's nothing in between the starting point and the empty tile, in this case we would simply break
                        There's at least one tile with different color in between, in this case the tile position would be a valid move
                        After both of these, we just break and move to the next direction
                        We check if the number of tiles in between by counting
                     */
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
                /*
                    Keep moving in the specified direction, while increment the count to
                    keep track of the number of tiles in between
                */
                nRow += dir[0];
                nCol += dir[1];
                count++;
            }
        }
    }

    /**
     * For this method, we look for possible moves by going from each occupied tile, in all 8 direction
     * If we managed to find a straight line of opposite color after the selected tile with the endpoint being
     * an empty tile, that tile will be a possible move
     * For example: B W W W, then position [4] would be a possible move
     *
     * @return the list of currently valid moves
     */
    /*@
        ensures (\forall int i; i > 0 && i < validMoves.size(); !validMoves.get(i - 1).equals(validMoves.get(i)));
        pure;
    */
    @Override
    public List<Move> getValidMoves() {
        //Initialize the move-lists
        validMoves.clear();
        validBlack.clear();
        validWhite.clear();
        //For every occupied tile, we do a directional check
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
    /*@
        ensures disk.equals(Disk.BLACK) ==> \result == validBlack;
        ensures disk.equals(Disk.WHITE) ==> \result == validWhite;
    */
    public List<Move> getValidMoves(Disk disk) {
        getValidMoves();
        if (disk.equals(Disk.BLACK))
            return validBlack;
        else
            return validWhite;
    }

    /**
     * Change turn to the opposite color
     */
    //@ensures current == \old(current.other());
    public void nextTurn() {
        current = current.other();
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
        ensures validBlack != \old(validBlack);
        ensures validWhite != \old(validWhite);
        ensures current == \old(current).other();
    */
    @Override
    public void doMove(Move move) {
        /*
            If the move is null, it's considered a passing move,
            therefore only switch turn without placing anything
         */
        if (move != null) {
            //Getting the coordinates and the disk color from the move object
            int row = ((OthelloMove) move).getRow();
            int col = ((OthelloMove) move).getCol();
            Disk disk = ((OthelloMove) move).getDisk();
            //If the move is valid, we execute the move
            if (isValidMove(move)) {
                //First place the disk in the coordinate
                board.setField(row, col, disk);
                //We iterate in 8 direction, looking for flippable lines
                for (int[] dir : dxy) {
                    int dRow = row + dir[0];
                    int dCol = col + dir[1];
                    int count = 0;
                    //Continue to iterate in that direction while the tile is of opposite color
                    while (board.isField(dRow, dCol)) {
                        if (board.getField(dRow, dCol).equals(disk.other())) {
                            //Continue to move in that direction while counting the tiles that traversed
                            dRow += dir[0];
                            dCol += dir[1];
                            count++;
                        } else {
                            //Once we encountered another tile or empty tile, break out immediately
                            break;
                        }
                    }
                    //We backtrack to the first tile, flipping all the disks in the middle
                    if (board.isField(dRow, dCol) && board.getField(dRow, dCol).equals(disk)) {
                        dRow -= dir[0];
                        dCol -= dir[1];
                        for (int i = 0; i < count; i++) {
                            board.flip(dRow, dCol);
                            dRow -= dir[0];
                            dCol -= dir[1];
                        }
                    }
                }
            }
        }
        validMoves = getValidMoves();
        nextTurn();
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
     * Sets the current board to a new board using a board object
     *
     * @param newBoard The new board as an object to change the current board
     */
    /*@
        ensures (\forall int i; i >= 0 && i <= 63; newBoard.getField(i) == board.getField(i));
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
