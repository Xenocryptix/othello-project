import Othello.Board;
import Othello.Disk;
import Othello.OthelloGame;
import Othello.OthelloMove;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class OthelloGameTest {
    private OthelloGame game;

    @BeforeEach
    public void setUp() {
        game = new OthelloGame();
    }

    @Test
    public void testFlipHorizontal() {
        Board board = game.getBoard();

        //Testing flip horizontal right
        assertEquals(board.getField(4, 4), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 5, 4));
        assertEquals(Disk.BLACK, board.getField(4, 4));

        //Testing flip horizontal left
        board.setField(3, 5, Disk.WHITE);
        board.flip(3, 4);

        assertEquals(board.getField(3, 4), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 2, 4));
        assertEquals(Disk.BLACK, board.getField(3, 4));
    }

    @Test
    public void testFlipVertical() {
        Board board = game.getBoard();

        //Testing flip vertical up
        assertEquals(board.getField(3, 3), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 3, 2));
        assertEquals(Disk.BLACK, board.getField(3, 3));

        //Testing flip vertical down
        assertEquals(board.getField(4, 4), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }

    @Test
    public void testFlipDiagonal() {
        Board board = game.getBoard();
        //Test flip diagonal NE direction
        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 5, 3));
        assertEquals(Disk.WHITE, board.getField(5, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 6, 2));
        assertEquals(Disk.BLACK, board.getField(5, 3));

        //Test flip diagonal NW direction
        game.doMove(new OthelloMove(Disk.WHITE, 6, 3));
        assertEquals(Disk.WHITE, board.getField(3, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 2));
        assertEquals(Disk.BLACK, board.getField(3, 3));

        board.reset();
        //Test flip diagonal SW direction
        game.doMove(new OthelloMove(Disk.BLACK, 3, 2));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 4));

        assertEquals(Disk.WHITE, board.getField(2, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 1, 5));
        assertEquals(Disk.BLACK, board.getField(2, 4));

        //Test flip diagonal SE direction
        //TODO: MIGHT NOT WORK CHECK
        assertEquals(Disk.WHITE, board.getField(4, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));

    }
}
