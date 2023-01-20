import Othello.Board;
import Othello.Disk;
import Othello.OthelloGame;
import Othello.OthelloMove;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class OthelloGameTest {
    private OthelloGame game;

    @BeforeEach
    public void setUp(){
        game = new OthelloGame();
    }

    @Test
    public void testFlipHorizontal() {
        Board board = game.getBoard();
        assertEquals(board.getField(4,4), Disk.WHITE);
        game.doMove(new OthelloMove(Disk.BLACK,5,4));
        assertEquals(Disk.BLACK, board.getField(4,4));
    }
}
