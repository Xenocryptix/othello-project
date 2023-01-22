import Othello.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class OthelloGameTest {
    private OthelloGame game;

    @BeforeEach
    public void setUp() {
        game = new OthelloGame();
    }
    @Disabled

    @Test
    public void testValidMoves() {
        assertEquals(game.getValidMoves().size(), 8);

        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 3,2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK,2,3)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 5,4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.BLACK, 4,5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE,2,4)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 3,5)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE, 4,2)));
        assertTrue(game.isValidMove(new OthelloMove(Disk.WHITE,5,3)));

        game.doMove(new OthelloMove(Disk.BLACK,4,5));
        game.doMove(new OthelloMove(Disk.WHITE,5,3));

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

    @Disabled

    @Test
    public void testFlipDiagonal() {
        Board board = game.getBoard();
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
    //TODO: Gameover
    //TODO: RANDOM MOVES GAME
    @Test
    public void fullRandomGame() {
        Board board = game.getBoard();
    }
}
