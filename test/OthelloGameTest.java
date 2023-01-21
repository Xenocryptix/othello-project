import Othello.Board;
import Othello.Disk;
import Othello.OthelloGame;
import Othello.OthelloMove;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
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
        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        assertEquals(Disk.BLACK, board.getField(4, 4));

        //Testing flip horizontal left
        board.setField(5, 3, Disk.WHITE);
        board.flip(4, 3);

        assertEquals(board.getField(4, 3), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 4, 2));
        assertEquals(Disk.BLACK, board.getField(4, 3));
    }

    @Disabled
    @Test
    public void testFlipVertical() {
        Board board = game.getBoard();

        //Testing flip vertical up
        assertEquals(board.getField(3, 3), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 2, 3));
        assertEquals(Disk.BLACK, board.getField(3, 3));

        //Testing flip vertical down
        assertEquals(board.getField(4, 4), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK, 5, 4));
        assertEquals(Disk.BLACK, board.getField(4, 4));
    }


    @Test
    public void testFlipDiagonal() {
        Board board = game.getBoard();
        //Test flip diagonal NE direction
        game.doMove(new OthelloMove(Disk.BLACK, 5, 4));
        game.doMove(new OthelloMove(Disk.WHITE, 3, 5));
        assertEquals(Disk.WHITE, board.getField(3, 5));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 5));
        assertEquals(Disk.BLACK, board.getField(3, 5));

        //Test flip diagonal NW direction
        game.doMove(new OthelloMove(Disk.WHITE, 3, 6));
        assertEquals(Disk.WHITE, board.getField(3, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 2));
        assertEquals(Disk.BLACK, board.getField(3, 3));

        board.reset();
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
}
