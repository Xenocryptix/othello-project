import Othello.*;
import Othello.ai.ComputerPlayer;
import Othello.ai.NaiveStrategy;
import Othello.ai.PlayerFactory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class OthelloGameTest {
    private OthelloGame game;
    private Board board;

    @BeforeEach
    public void setUp() {
        game = new OthelloGame();
        board = game.getBoard();
    }

    @Test
    public void testValidMoves() {
        assertEquals(game.getValidMoves().size(), 8);

        //Ensuring that validMoves contains all the valid moves for the black disk
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 2, 3)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 5)));

        //Ensuring that validMoves contains all the valid moves for the black disk
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 2, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 3, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 4, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 5, 3)));

        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 5, 3));

        assertEquals(game.getValidMoves().size(), 9);

        //Ensuring that validMoves contains all the valid moves for the black disk after making two moves
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 2, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 6, 2)));

        //Ensuring that validMoves contains all the valid moves for the black disk after making two moves
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 3, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 4, 6)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 5, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 2, 5)));

        game.reset();
        game.doMove(new OthelloMove(Disk.BLACK, 2, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 2));

        assertEquals(9, game.getValidMoves().size());

        //Ensuring that validMoves contains all the valid moves for the black disk after resetting and doing two moves
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 2, 1)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 5)));
        assertFalse(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 3)));
        assertFalse(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 2)));

        //Ensuring that validMoves contains all the valid moves for the black disk after resetting and doing two moves
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
     * Test that when multiple flips occur at the same time it flips
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
    }

    //TODO: Gameover

    @Test
    public void fullRandomGame() {
        assertFalse(game.isGameover());
        AbstractPlayer player1 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        AbstractPlayer player2 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        game.setPlayer1(player1);
        game.setPlayer2(player2);


        assertEquals(Disk.BLACK, game.getCurrentDisk());
        game.doMove(player1.determineMove(game));
        assertTrue(board.countDisk(Disk.BLACK) > board.countDisk(Disk.WHITE));
        assertEquals(Disk.WHITE, game.getCurrentDisk());

        int oldCount = board.countDisk(Disk.WHITE);
        game.doMove(player2.determineMove(game));
        assertTrue(board.countDisk(Disk.WHITE) > oldCount);
        assertEquals(board.countDisk(Disk.WHITE), board.countDisk(Disk.BLACK));
        assertEquals(Disk.BLACK, game.getCurrentDisk());

        while (!game.isGameover()) {
            if (!game.isGameover())
                game.doMove(player1.determineMove(game));
            if (!game.isGameover())
                game.doMove(player2.determineMove(game));
        }

        assertTrue(game.isGameover());
        if (board.countDisk(Disk.BLACK) > board.countDisk(Disk.WHITE)) {
            assertEquals(player1, game.getWinner());
        } else if (board.countDisk(Disk.BLACK) < board.countDisk(Disk.WHITE)){
            assertEquals(player2, game.getWinner());
        } else {
            assertNull(game.getWinner());
        }

    }

    /**
     * This test would go through possible board representations for game ending before the board is full
     */
    @Test
    public void gameOverNotFull() {
        /**
         * The following will be a representation of the board when there are no possible
         * moves available for both discs but he board is not full
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

}
