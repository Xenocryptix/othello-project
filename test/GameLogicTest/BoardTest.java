package GameLogicTest;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import othello.exceptions.InvalidNumber;
import othello.model.Board;
import othello.model.Disk;
import othello.model.OthelloMove;

import static org.junit.jupiter.api.Assertions.*;

public class BoardTest {
    private Board board;


    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    /**
     * Ensure that the setup of the game is correct where the middle tiles are set correctly to white and black
     * while other tiles are empty
     */
    @Test
    public void testSetup() {
        assertEquals(Disk.BLACK, board.getField(3, 4));
        assertEquals(Disk.BLACK, board.getField(4, 3));
        assertEquals(Disk.WHITE, board.getField(3, 3));
        assertEquals(Disk.WHITE, board.getField(4, 4));
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                if (i != 3 && j != 3 && i != 4 && j != 4) {
                    assertEquals(Disk.EMPTY, board.getField(i, j));
                }
            }
        }
    }

    /**
     * Ensures that converting from (row,col) pair work's correctly
     *
     * @throws InvalidNumber if the number doesn't lien in the correct range
     */
    @Test
    public void testIndex() throws InvalidNumber {
        int index = 0;
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                assertEquals(index, board.index(i, j));
                index += 1;
            }
        }
    }

    /**
     * Ensures that all fields of the board are from 0 till Board.DIM * Board.DIM
     *
     * @throws InvalidNumber if the number doesn't lien in the correct range
     */
    @Test
    public void testIsFieldIndex() throws InvalidNumber {
        assertThrows(InvalidNumber.class, () -> board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(Board.DIM * Board.DIM - 1));
        assertThrows(InvalidNumber.class, () -> board.isField(Board.DIM * Board.DIM));
    }

    /**
     * Ensures that the board has fields at row and column 0 till Board.DIM - 1
     */
    @Test
    public void testIsFieldRowCol() {
        assertFalse(board.isField(0, -1));
        assertFalse(board.isField(-1, 0));
        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(Board.DIM - 1, Board.DIM - 1));
        assertFalse(board.isField(7, Board.DIM + 1));
        assertFalse(board.isField(Board.DIM + 1, 7));
    }

    /**
     * Ensures that setting a field with index to a disk works
     */
    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(0, Disk.WHITE);
        assertEquals(Disk.WHITE, board.getField(0));
        assertEquals(Disk.EMPTY, board.getField(1));
    }

    /**
     * Ensures that setting a field with row and col to a disk work
     *
     * @throws InvalidNumber if the number doesn't lien in the correct range
     */
    @Test
    public void testSetAndGetFieldRowCol() throws InvalidNumber {
        board.setField(0, 0, Disk.BLACK);
        assertEquals(Disk.BLACK, board.getField(0, 0));
        assertEquals(Disk.EMPTY, board.getField(0, 1));
        assertEquals(Disk.EMPTY, board.getField(1, 0));
        assertEquals(Disk.EMPTY, board.getField(1, 1));
    }

    /**
     * Ensures that flipping a field with index works
     */
    @Test
    public void testFlipIndex() {
        //Flipping a white field
        assertEquals(Disk.WHITE, board.getField(27));
        board.flip(27);
        assertEquals(Disk.BLACK, board.getField(27));

        //Flipping a black field
        assertEquals(Disk.BLACK, board.getField(28));
        board.flip(28);
        assertEquals(Disk.WHITE, board.getField(28));

        //Flipping an empty field
        assertEquals(Disk.EMPTY, board.getField(0));
        board.flip(0);
        assertEquals(Disk.EMPTY, board.getField(0));
    }

    /**
     * Ensures flipping a field with row and col works
     */
    @Test
    public void testFlipRowCol() {
        //Flipping a white field
        assertEquals(Disk.WHITE, board.getField(3, 3));
        board.flip(3, 3);
        assertEquals(Disk.BLACK, board.getField(3, 3));

        //Flipping a black field
        assertEquals(Disk.BLACK, board.getField(4, 3));
        board.flip(4, 3);
        assertEquals(Disk.WHITE, board.getField(4, 3));

        //Flipping an empty field
        assertEquals(Disk.EMPTY, board.getField(0, 0));
        board.flip(0, 0);
        assertEquals(Disk.EMPTY, board.getField(0, 0));
    }

    /**
     * Test if flipping in the two directions horizontally to the right works correctly
     */
    @Test
    public void testFlipMoveHorizontalRight() {
        assertEquals(Disk.WHITE, board.getField(4, 4));
        board.flipMove(new OthelloMove(Disk.BLACK, 4, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }

    /**
     * Test if flipping in the two directions horizontally to the left works correctly
     */
    @Test
    public void testFlipMoveHorizontalLeft() {
        assertEquals(Disk.WHITE, board.getField(3, 3));
        board.flipMove(new OthelloMove(Disk.BLACK, 3, 2));
        assertEquals(Disk.BLACK, board.getField(3, 3));
    }

    /**
     * Test if flipping in the two directions vertically upwards works correctly
     */

    @Test
    public void testFlipMoveVerticalUp() {
        assertEquals(Disk.WHITE, board.getField(3, 3));
        board.flipMove(new OthelloMove(Disk.BLACK, 2, 3));
        assertEquals(Disk.BLACK, board.getField(3, 3));
    }

    /**
     * Test if flipping in the two directions vertically downwards works correctly
     */

    @Test
    public void testFlipMoveVerticalDown() {
        assertEquals(Disk.WHITE, board.getField(4, 4));
        board.flipMove(new OthelloMove(Disk.BLACK, 5, 4));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }

    /**
     * Test if flipping is performed correctly in the north direction
     */

    @Test
    public void testFlipMoveDiagonalNorth() {
        //Test flip diagonal NE direction
        board.flipMove(new OthelloMove(Disk.BLACK, 5, 4));
        board.flipMove(new OthelloMove(Disk.WHITE, 3, 5));

        assertEquals(Disk.WHITE, board.getField(3, 4));
        board.flipMove(new OthelloMove(Disk.BLACK, 2, 5));
        assertEquals(Disk.BLACK, board.getField(3, 4));

        //Test flip diagonal NW direction
        board.flipMove(new OthelloMove(Disk.WHITE, 3, 6));

        assertEquals(Disk.WHITE, board.getField(3, 3));
        board.flipMove(new OthelloMove(Disk.BLACK, 2, 2));
        assertEquals(Disk.BLACK, board.getField(3, 3));

    }

    /**
     * Test if flipping works correctly in the south direction
     */
    @Test
    public void testFlipMoveDiagonalSouth() {
        //Test flip diagonal SW direction
        board.flipMove(new OthelloMove(Disk.BLACK, 2, 3));
        board.flipMove(new OthelloMove(Disk.WHITE, 4, 2));

        assertEquals(Disk.WHITE, board.getField(4, 2));
        board.flipMove(new OthelloMove(Disk.BLACK, 5, 1));
        assertEquals(Disk.BLACK, board.getField(4, 2));

        //Test flip diagonal SE direction
        assertEquals(Disk.WHITE, board.getField(4, 4));
        board.flipMove(new OthelloMove(Disk.BLACK, 5, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }

    /**
     * Test that when multiple flips occur at the same time it flips the correct disks
     *
     * @throws InvalidNumber if the number doesn't lien in the correct range
     */
    @Test
    public void testMultipleFlips() throws InvalidNumber {
        //Setting up the board for a move that flips more than one field
        board.flipMove(new OthelloMove(Disk.BLACK, 3, 2));
        board.flipMove(new OthelloMove(Disk.WHITE, 4, 2));

        assertEquals(Disk.WHITE, board.getField(4, 2));
        assertEquals(Disk.WHITE, board.getField(4, 3));
        board.flipMove(new OthelloMove(Disk.BLACK, 5, 2));

        assertEquals(Disk.BLACK, board.getField(4, 2));
        assertEquals(Disk.BLACK, board.getField(4, 3));

        board.flipMove(new OthelloMove(Disk.WHITE, 4, 1));

        assertEquals(Disk.WHITE, board.getField(4, 2));
        assertEquals(Disk.WHITE, board.getField(4, 3));

        board.reset();

        //An edge case for flipping
        /*
           A   B   C   D   E   F   G   H
        1  B |   |   |   |   |   |   |
          ---+---+---+---+---+---+---+---
        2    | W |   |   |   |   |   | B
          ---+---+---+---+---+---+---+---
        3    |   | B |   |   |   | W |
          ---+---+---+---+---+---+---+---
        4    |   |   | W |   | W |   |
          ---+---+---+---+---+---+---+---
        5  B | W |   | W |   | W | W | W
          ---+---+---+---+---+---+---+---
        6    |   |   | B |   |   |   |
          ---+---+---+---+---+---+---+---
        7    |   | W |   |   |   | W |
          ---+---+---+---+---+---+---+---
        8    | B |   |   |   |   |   | B
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

        //Ensuring that the fields that contain white before the flip are actually white
        assertEquals(Disk.WHITE, board.getField(3, 3));
        assertEquals(Disk.WHITE, board.getField(3, 5));
        assertEquals(Disk.WHITE, board.getField(2, 6));

        //Ensuring that the fields that contain white before the flip are actually white and these shouldn't be flipped
        assertEquals(Disk.WHITE, board.getField(4, 1));
        assertEquals(Disk.WHITE, board.getField(4, 3));
        assertEquals(Disk.WHITE, board.getField(6, 6));

        //Placing black disk at E5
        board.flipMove(new OthelloMove(Disk.BLACK, 4, 4));

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
     * Tests when there is a winner in the board. This is when a disk
     * has more disks than another disk
     */
    @Test
    public void testWinning() {
        assertFalse(board.hasWinner());

        board.setField(0, Disk.WHITE);
        assertTrue(board.hasWinner());
        assertTrue(board.isWinner(Disk.WHITE));
        assertFalse(board.isWinner(Disk.BLACK));

        board.setField(0, Disk.BLACK);
        assertTrue(board.isWinner(Disk.BLACK));
        assertFalse(board.isWinner(Disk.WHITE));
    }

    /**
     * Ensures after a reset is made that the board is back to it is
     * original initialisation
     */
    @Test
    public void testReset() {
        board.setField(0, Disk.WHITE);
        board.setField(Board.DIM * Board.DIM - 1, Disk.BLACK);
        board.reset();
        assertEquals(Disk.EMPTY, board.getField(0));
        assertEquals(Disk.EMPTY, board.getField(Board.DIM * Board.DIM - 1));
        assertEquals(Disk.BLACK, board.getField(3, 4));
        assertEquals(Disk.BLACK, board.getField(4, 3));
        assertEquals(Disk.WHITE, board.getField(3, 3));
        assertEquals(Disk.WHITE, board.getField(4, 4));
    }

    /**
     * Ensures that changes made on a deep copy of the board do not affect the
     * original board
     */
    @Test
    public void testDeepCopy() {
        board.setField(0, Disk.WHITE);
        board.setField(Board.DIM * Board.DIM - 1, Disk.BLACK);
        Board deepCopyBoard = board.deepCopy();

        // First test if all the fields are the same
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            assertEquals(board.getField(i), deepCopyBoard.getField(i));
        }

        // Check if a field in the deepcopied board the original remains the same
        deepCopyBoard.setField(0, Disk.BLACK);

        assertEquals(Disk.WHITE, board.getField(0));
        assertEquals(Disk.BLACK, deepCopyBoard.getField(0));
    }

    /**
     * Tests the condition where the board is full
     */
    @Test
    public void testFull() {
        assertFalse(board.isFull());

        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            board.setField(i, Disk.BLACK);
        }

        assertTrue(board.isFull());

    }
}

