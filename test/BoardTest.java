import Othello.Board;
import Othello.Disk;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class BoardTest {
    private Board board;


    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    @Test
    public void testIndex() {
        int index = 0;
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                assertEquals(index, board.index(i, j));
                index += 1;
            }
        }
    }

    @Test
    public void testIsFieldIndex() {
        assertFalse(board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(Board.DIM * Board.DIM - 1));
        assertFalse(board.isField(Board.DIM * Board.DIM));
    }

    @Test
    public void testIsFieldRowCol() {
        assertFalse(board.isField(-1, 0));
        assertFalse(board.isField(0, -1));
        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(7, 7));
        assertFalse(board.isField(7, 8));
        assertFalse(board.isField(8, 7));
    }

    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(0, Disk.WHITE);
        assertEquals(Disk.WHITE, board.getField(0));
        assertEquals(Disk.EMPTY, board.getField(1));
    }

    @Test
    public void testSetAndGetFieldRowCol() {
        board.setField(0, 0, Disk.BLACK);
        assertEquals(Disk.BLACK, board.getField(0, 0));
        assertEquals(Disk.EMPTY, board.getField(0, 1));
        assertEquals(Disk.EMPTY, board.getField(1, 0));
        assertEquals(Disk.EMPTY, board.getField(1, 1));
    }

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

    @Test
    public void testFull() {
        assertFalse(board.isFull());

        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            board.setField(i, Disk.BLACK);
        }

        assertTrue(board.isFull());

    }
}

