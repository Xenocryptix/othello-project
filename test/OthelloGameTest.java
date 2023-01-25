import Othello.model.*;
import Othello.players.AbstractPlayer;
import Othello.players.ai.NaiveStrategy;
import Othello.players.PlayerFactory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

public class OthelloGameTest {
    private OthelloGame game;
    private Board board;

    @BeforeEach
    public void setUp() {
        game = new OthelloGame();
        board = game.getBoard();
    }

    /**
     * Tests that the valid moves generated by the valid moves method work as expected
     */
    @Test
    public void testValidMoves() {
        //Testing that the size of the array valid moves equals 8 eliminates cases where an extra invalid move is generated
        assertEquals(game.getValidMoves().size(), 8);

        //Ensuring that validMoves contains all the valid moves for the black disk
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 2, 3)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 5)));

        //Ensuring that validMoves contains all the valid moves for the white disk
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 2, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 3, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 4, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 5, 3)));

        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 5, 3));

        //Testing that the size of the array valid moves equals 9 eliminates cases where an extra invalid move is generated
        assertEquals(game.getValidMoves().size(), 9);

        //Ensuring that validMoves contains all the valid moves for the black disk after making two moves
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 2, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 6, 2)));

        //Ensuring that validMoves contains all the valid moves for the white disk after making two moves
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 3, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 4, 6)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 5, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 2, 5)));

        game.reset();
        game.doMove(new OthelloMove(Disk.BLACK, 2, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 2));

        //Testing that the size of the array valid moves equals 9 eliminates cases where an extra invalid move is generated
        assertEquals(9, game.getValidMoves().size());

        //Ensuring that validMoves contains all the valid moves for the black disk after resetting and doing two moves
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 2, 1)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 5)));
        assertFalse(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 3)));
        assertFalse(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 2)));

        //Ensuring that validMoves contains all the valid moves for the white disk after resetting and doing two moves
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 2, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 1, 3)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 3, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 5, 3)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 4, 2)));
        assertFalse(game.isValidMove(new OthelloMove(Disk.WHITE, 1, 1)));
        assertFalse(game.isValidMove(new OthelloMove(Disk.WHITE, 5, 5)));
    }

    /**
     * Test if flipping in the two directions horizontally to the right works correctly
     */
    @Test
    public void testFlipHorizontalRight() {
        assertEquals(Disk.WHITE, board.getField(4, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }

    /**
     * Test if flipping in the two directions horizontally to the left works correctly
     */
    @Test
    public void testFlipHorizontalLeft() {
        assertEquals(Disk.WHITE, board.getField(3, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 3, 2));
        assertEquals(Disk.BLACK, board.getField(3, 3));
    }

    /**
     * Test if flipping in the two directions vertically upwards works correctly
     */

    @Test
    public void testFlipVerticalUp() {
        assertEquals(Disk.WHITE, board.getField(3, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 3));
        assertEquals(Disk.BLACK, board.getField(3, 3));
    }

    /**
     * Test if flipping in the two directions vertically downwards works correctly
     */

    @Test
    public void testFlipVerticalDown() {
        assertEquals(Disk.WHITE, board.getField(4, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 4));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }

    /**
     * Test if flipping is performed correctly in the north direction
     */

    @Test
    public void testFlipDiagonalNorth() {
        //Test flip diagonal NE direction
        game.doMove(new OthelloMove(Disk.BLACK, 5, 4));
        game.doMove(new OthelloMove(Disk.WHITE, 3, 5));
        assertEquals(Disk.WHITE, board.getField(3, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 5));
        assertEquals(Disk.BLACK, board.getField(3, 4));

        //Test flip diagonal NW direction
        game.doMove(new OthelloMove(Disk.WHITE, 3, 6));
        assertEquals(Disk.WHITE, board.getField(3, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 2));
        assertEquals(Disk.BLACK, board.getField(3, 3));

    }

    /**
     * Test if flipping works correctly in the south direction
     */
    @Test
    public void testFlipDiagonalSouth() {
        //Test flip diagonal SW direction
        game.doMove(new OthelloMove(Disk.BLACK, 2, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 4, 2));

        assertEquals(Disk.WHITE, board.getField(4, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 1));
        assertEquals(Disk.BLACK, board.getField(4, 2));

        //Test flip diagonal SE direction
        assertEquals(Disk.WHITE, board.getField(4, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }

    /**
     * Test that when multiple flips occur at the same time it flips the correct disks
     */
    @Test
    public void testMultipleFlips() {
        //Setting up the board for a move that flips more than one field
        game.doMove(new OthelloMove(Disk.BLACK, 3, 2));
        game.doMove(new OthelloMove(Disk.WHITE, 4, 2));

        assertEquals(Disk.WHITE, board.getField(4, 2));
        assertEquals(Disk.WHITE, board.getField(4, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 2));
        assertEquals(Disk.BLACK, board.getField(4, 2));
        assertEquals(Disk.BLACK, board.getField(4, 3));

        game.doMove(new OthelloMove(Disk.WHITE, 4, 1));
        assertEquals(Disk.WHITE, board.getField(4, 2));
        assertEquals(Disk.WHITE, board.getField(4, 3));

        game.reset();

        //An edge case where the for flipping
        /**
         *    A   B   C   D   E   F   G   H
         * 1  B |   |   |   |   |   |   |
         *   ---+---+---+---+---+---+---+---
         * 2    | W |   |   |   |   |   | B
         *   ---+---+---+---+---+---+---+---
         * 3    |   | B |   |   |   | W |
         *   ---+---+---+---+---+---+---+---
         * 4    |   |   | W |   | W |   |
         *   ---+---+---+---+---+---+---+---
         * 5  B | W |   | W |   | W | W | W
         *   ---+---+---+---+---+---+---+---
         * 6    |   |   | B |   |   |   |
         *   ---+---+---+---+---+---+---+---
         * 7    |   | W |   |   |   | W |
         *   ---+---+---+---+---+---+---+---
         * 8    | B |   |   |   |   |   | B
         */

        //Setting up the board to match the above diagram
        board.setField(0, Disk.BLACK);
        board.setField(4, 0, Disk.BLACK);
        board.setField(7, 1, Disk.BLACK);
        board.setField(1, 7, Disk.BLACK);
        board.setField(7, 7, Disk.BLACK);
        board.setField(5, 3, Disk.BLACK);
        board.setField(1, 1, Disk.WHITE);
        board.setField(2, 2, Disk.BLACK);
        board.setField(4, 3, Disk.WHITE);
        board.setField(4, 4, Disk.EMPTY);
        board.setField(3, 4, Disk.EMPTY);
        board.setField(2, 6, Disk.WHITE);
        board.setField(3, 5, Disk.WHITE);
        board.setField(4, 1, Disk.WHITE);
        board.setField(4, 3, Disk.WHITE);
        board.setField(4, 5, Disk.WHITE);
        board.setField(4, 6, Disk.WHITE);
        board.setField(4, 7, Disk.WHITE);
        board.setField(6, 2, Disk.WHITE);
        board.setField(6, 6, Disk.WHITE);
        //Updating valid moves
        game.getValidMoves();

        //Ensuring that the fields that contain white before the flip are actually white
        assertEquals(Disk.WHITE, board.getField(3, 3));
        assertEquals(Disk.WHITE, board.getField(3, 5));
        assertEquals(Disk.WHITE, board.getField(2, 6));

        //Ensuring that the fields that contain white before the flip are actually white and these shouldn't be flipped
        assertEquals(Disk.WHITE, board.getField(4, 1));
        assertEquals(Disk.WHITE, board.getField(4, 3));
        assertEquals(Disk.WHITE, board.getField(6, 6));

        //Placing black disk at E5
        game.doMove(new OthelloMove(Disk.BLACK, 4, 4));

        //Ensuring that the correct tiles that should be flipped are actually flipped
        assertEquals(Disk.BLACK, board.getField(3, 3));
        assertEquals(Disk.BLACK, board.getField(3, 5));
        assertEquals(Disk.BLACK, board.getField(2, 6));

        //Ensuring that the tiles that should not be flipped stay the same
        assertEquals(Disk.WHITE, board.getField(4, 1));
        assertEquals(Disk.WHITE, board.getField(4, 3));
        assertEquals(Disk.WHITE, board.getField(6, 6));

    }

    /**
     * A test to ensure that when a board is full there are no valid moves available to be played by both players
     */
    @Test
    public void testGameOverFull() {
        assertFalse(game.isGameover());
        assertTrue(game.getValidMoves().size() > 0);

        //Add random disks to fill the board
        Random rand = new Random();
        Disk disk;
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            if (rand.nextInt() % 2 == 0)
                disk = Disk.BLACK;
            else
                disk = Disk.WHITE;
            board.setField(i, disk);
        }

        //Ensures that there are no valid moves and game is over
        assertEquals(0, game.getValidMoves().size());
        assertTrue(game.isGameover());
    }

    /**
     * Ensures that setting the game board to a new board changes the game board
     */
    @Test
    public void testSetBoard() {
        //Creating a new board to set the game board to
        Board changedBoard = new Board();
        changedBoard.setField(0, Disk.BLACK);

        //Ensuring that the first index is empty
        assertEquals(Disk.EMPTY, board.getField(0));
        game.setBoard(changedBoard);
        Board newBoard = game.getBoard();

        //Ensuring that the first index is changed to the disk of the board that was set to it
        assertEquals(Disk.BLACK, newBoard.getField(0));
    }

    /**
     * Ensuring that after a move is played the player's turn switches
     */
    @Test
    public void testGetTurn() {
        AbstractPlayer player1 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        AbstractPlayer player2 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        game.setPlayer1(player1);
        game.setPlayer2(player2);

        assertEquals(player1, game.getTurn());
        game.doMove(player1.determineMove(game));
        assertEquals(player2, game.getTurn());

    }
    /**
     * This test would go through possible board representations for game ending before the board is full
     */
    @Test
    public void gameOverNotFull() {
        /**
         * The following will be a representation of the board when there are no possible
         * moves available for both discs when the board is not full
         *
         *    A   B   C   D   E   F   G   H
         * 1  W | W | W | W | W | W | W | W
         *   ---+---+---+---+---+---+---+---
         * 2  W | W | W | W | W | W | W | W
         *   ---+---+---+---+---+---+---+---
         * 3  W | W | W | W | W | W | W | W
         *   ---+---+---+---+---+---+---+---
         * 4  W | W | W | W | W | W | W |
         *   ---+---+---+---+---+---+---+---
         * 5  W | W | W | W | W | W |   |
         *   ---+---+---+---+---+---+---+---
         * 6  W | W | W | W | W | W |   | B
         *   ---+---+---+---+---+---+---+---
         * 7  W | W | W | W | W | W | W |
         *   ---+---+---+---+---+---+---+---
         * 8  W | W | W | W | W | W | W | W
         */
        assertFalse(game.isGameover());
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            if (i != 31 && i != 39 && i != 47 && i != 55 && i != 46 && i != 38) {
                board.setField(i, Disk.WHITE);
            }
            if (i == 47) {
                board.setField(i, Disk.BLACK);
            }
        }
        assertFalse(board.isFull());
        assertTrue(game.isGameover());

        game.reset();
        /**
         * The following will be another representation of the board when there are no possible
         * moves available for both discs but he board is not full
         *
         *    A   B   C   D   E   F   G   H
         * 1    | B | B | B | B | B | B | B
         *   ---+---+---+---+---+---+---+---
         * 2    | W | W | W | W | W |   | B
         *   ---+---+---+---+---+---+---+---
         * 3  W | W | W | W | W | W | W | B
         *   ---+---+---+---+---+---+---+---
         * 4  W | W | W | W | W | W | W | B
         *   ---+---+---+---+---+---+---+---
         * 5  W | W | W | W | W | W | W | B
         *   ---+---+---+---+---+---+---+---
         * 6  W | W | W | W | W | W | W | B
         *   ---+---+---+---+---+---+---+---
         * 7  W | W | W | W | W | W | W | B
         *   ---+---+---+---+---+---+---+---
         * 8    | W | W | W | W | W |   |
         */

        assertFalse(game.isGameover());
        for (int i = 16; i < 55; i++) {
            board.setField(i, Disk.WHITE);
        }
        for (int i = 9; i < 14; i++) {
            board.setField(i, Disk.WHITE);
        }
        for (int i = 57; i < 62; i++) {
            board.setField(i, Disk.WHITE);
        }
        for (int i = 1; i < 7; i++) {
            board.setField(i, Disk.BLACK);
        }
        for (int i = 7; i <= 55; i = i + 8) {
            board.setField(i, Disk.BLACK);
        }
        assertFalse(board.isFull());
        assertTrue(game.isGameover());
    }

    /**
     * A full game is player between two computer players that play a random valid move.
     * The test ensures that while the game is not over that player 1 and player 2 both play
     * moves until both of them do not have any valid moves remaining and checks the winner
     * at the end if there's a winner
     */
    @Test
    public void fullRandomGame() {
        assertFalse(game.isGameover());
        AbstractPlayer player1 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        AbstractPlayer player2 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        game.setPlayer1(player1);
        game.setPlayer2(player2);

        //Allows both players to make moves while the game is not over
        Move move;
        //Get the disk of the current turn
        Disk disk = game.getCurrentDisk();
        while (!game.isGameover()) {
//            System.out.println("P1 moving");
            move = player1.determineMove(game);
            game.doMove(move);
//            System.out.println("P2 moving");
            move = player2.determineMove(game);
            game.doMove(move);
            //Since 2 turns happen in each loop, the disk color will be flipped 2 times,
            //therefore stays the same
            assertEquals(disk, game.getCurrentDisk());
        }

        assertTrue(game.isGameover());
        if (board.isWinner(Disk.BLACK)) {
            assertEquals(player1, game.getWinner());
        } else if (board.isWinner(Disk.WHITE)) {
            assertEquals(player2, game.getWinner());
        } else if (!board.hasWinner()) {
            assertNull(game.getWinner());
        }

    }

}
