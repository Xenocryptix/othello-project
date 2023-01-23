import Othello.Board;
import Othello.Disk;
import Othello.OthelloGame;
import Othello.OthelloMove;
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

        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 2, 3)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 2, 4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 3, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 4, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 5, 3)));

        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 5, 3));

        assertEquals(game.getValidMoves().size(), 9);
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 2, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5, 2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 3, 5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 4, 6)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 5, 5)));
        //TODO: ADD LAST
    }

    /**
     * Test if flipping in the two directions horizontally works correctly, i.e. right and left
     */
    @Test
    public void testFlipHorizontal() {
        //Testing flip horizontal right
        assertEquals(board.getField(4, 4), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));

        //Testing flip horizontal left
        game.doMove(new OthelloMove(Disk.WHITE, 5, 3));

        assertEquals(board.getField(4, 3), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 4, 2));
        assertEquals(Disk.BLACK, board.getField(4, 3));
    }

    /**
     * Test if flipping in the two directions vertically works correctly, i.e. up and down
     */

    @Test
    public void testFlipVertical() {
        //Testing flip vertical up
        assertEquals(board.getField(3, 3), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 2, 3));
        assertEquals(Disk.BLACK, board.getField(3, 3));

        //Testing flip vertical down
        assertEquals(board.getField(4, 4), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 5, 4));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }

    /**
     * Test if flipping is performed directly in all 4 diagonal directions, i.e. North East, North West, South West and South East
     */

    @Test
    public void testFlipDiagonal() {
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

        game.reset();
        //Test flip diagonal SW direction
        game.doMove(new OthelloMove(Disk.BLACK, 2, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 4, 2));

        assertEquals(Disk.WHITE, board.getField(4, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 1));
        assertEquals(Disk.BLACK, board.getField(4, 2));

        //Test flip diagonal SE direction
        //TODO: MIGHT NOT WORK CHECK
        assertEquals(Disk.WHITE, board.getField(4, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));

    }

    //TODO: Gameover
    //TODO: RANDOM MOVES GAME
    @Test
    public void fullRandomGame() {
        assertFalse(game.isGameover());

        game.doMove(game.getRandomValidMove(Disk.BLACK));
        assertTrue(board.countDisk(Disk.BLACK) > board.countDisk(Disk.WHITE));

        game.doMove(game.getRandomValidMove(Disk.WHITE));


        assertTrue(game.isGameover());

    }

    /**
     * This test would go through possible board representations for gmae ending before the board is full
     */
    @Test
    public void gameOverNotFull() {
        /**
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
