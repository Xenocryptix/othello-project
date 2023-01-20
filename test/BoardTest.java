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
    public void testSetup() {
        assertEquals(Disk.BLACK, board.getField(3, 4));
        assertEquals(Disk.BLACK, board.getField(4, 4));
        assertEquals(Disk.WHITE, board.getField(3, 3));
        assertEquals(Disk.WHITE, board.getField(4, 3));
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
        assertEquals(Disk.BLACK, board.getField(4, 4));
        assertEquals(Disk.WHITE, board.getField(3, 3));
        assertEquals(Disk.WHITE, board.getField(4, 3));
    }
}
