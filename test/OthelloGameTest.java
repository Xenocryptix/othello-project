import Othello.model.*;
import Othello.players.AbstractPlayer;
import Othello.players.PlayerFactory;
import Othello.players.ai.NaiveStrategy;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class OthelloGameTest {
    private OthelloGame game;
    private Board board;

    @BeforeEach
    public void setUp() {
        game = new OthelloGame();
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
     * A test to ensure that when a board is full there are no valid moves available to be played by both players
     */
    @Test
    public void testGameOverFull() {
        assertFalse(game.isGameover());
        assertTrue(game.getValidMoves().size() > 0);

        //Place moves until the board is full
        game.doMove(new OthelloMove(Disk.BLACK, 3, 2));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 1, 2));
        game.doMove(new OthelloMove(Disk.WHITE, 4, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 2));
        game.doMove(new OthelloMove(Disk.WHITE, 4, 1));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 4));
        game.doMove(new OthelloMove(Disk.WHITE, 0, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 3, 1));
        game.doMove(new OthelloMove(Disk.WHITE, 4, 5));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 6));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 3, 0));
        game.doMove(new OthelloMove(Disk.BLACK, 4, 0));
        game.doMove(new OthelloMove(Disk.WHITE, 6, 5));
        game.doMove(new OthelloMove(Disk.BLACK, 6, 4));
        game.doMove(new OthelloMove(Disk.WHITE, 7, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 1, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 6, 7));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 0));
        game.doMove(new OthelloMove(Disk.WHITE, 6, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 3, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 1, 5));
        game.doMove(new OthelloMove(Disk.BLACK, 6, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 1, 1));
        game.doMove(new OthelloMove(Disk.WHITE, 0, 0));
        game.doMove(new OthelloMove(Disk.BLACK, 1, 6));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 1));
        game.doMove(new OthelloMove(Disk.BLACK, 4, 6));
        game.doMove(new OthelloMove(Disk.WHITE, 1, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 0, 6));
        game.doMove(new OthelloMove(Disk.WHITE, 3, 6));
        game.doMove(new OthelloMove(Disk.WHITE, 3, 6));
        game.doMove(new OthelloMove(Disk.WHITE, 1, 7));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 7));

        assertFalse(game.isGameover());

        game.doMove(new OthelloMove(Disk.WHITE, 5, 1));
        game.doMove(new OthelloMove(Disk.BLACK, 0, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 4, 7));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 6));
        game.doMove(new OthelloMove(Disk.BLACK, 0, 7));
        game.doMove(new OthelloMove(Disk.WHITE, 7, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 7, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 5, 0));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 7));
        game.doMove(new OthelloMove(Disk.WHITE, 1, 0));
        game.doMove(new OthelloMove(Disk.BLACK, 6, 1));
        game.doMove(new OthelloMove(Disk.WHITE, 6, 0));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 0, 1));
        game.doMove(new OthelloMove(Disk.BLACK, 7, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 7, 6));
        game.doMove(new OthelloMove(Disk.BLACK, 6, 6));
        game.doMove(new OthelloMove(Disk.WHITE, 3, 7));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 7));
        game.doMove(new OthelloMove(Disk.WHITE, 7, 7));
        game.doMove(new OthelloMove(Disk.BLACK, 7, 1));
        game.doMove(new OthelloMove(Disk.WHITE, 7, 0));
        game.doMove(new OthelloMove(Disk.BLACK, 0, 1));
        game.doMove(new OthelloMove(Disk.WHITE,0,3));
        game.doMove(new OthelloMove(Disk.BLACK,0,4));


        //Ensures that there are no valid moves and game is over
        assertEquals(0, game.getValidMoves().size());
        assertTrue(game.isGameover());
    }

    /**
     * This test would go through possible board representations for game ending before the board is full
     */
    @Test
    public void gameOverNotFull() {
        /*
        The following will be a representation of the board when there are no possible
        moves available for both discs when the board is not full
            A   B   C   D   E   F   G   H
        1    |   |   |   |   |   |   |
          ---+---+---+---+---+---+---+---
        2    |   |   |   |   |   |   |
          ---+---+---+---+---+---+---+---
        3    |   |   |   | B |   |   |
          ---+---+---+---+---+---+---+---
        4    |   |   | B | B | B |   |
          ---+---+---+---+---+---+---+---
        5    |   | B | B | B | B | B |
          ---+---+---+---+---+---+---+---
        6    |   |   | B |   | B |   |
          ---+---+---+---+---+---+---+---
        7    |   |   |   | B |   |   |
          ---+---+---+---+---+---+---+---
        8    |   |   |   |   |   |   |
         */
        assertFalse(game.isGameover());

        game.doMove(new OthelloMove(Disk.BLACK, 4, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 5, 3));
        game.doMove(new OthelloMove(Disk.BLACK, 4, 2));
        game.doMove(new OthelloMove(Disk.WHITE, 5, 5));
        game.doMove(new OthelloMove(Disk.BLACK, 6, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 3, 5));
        game.doMove(new OthelloMove(Disk.BLACK, 4, 6));
        game.doMove(new OthelloMove(Disk.BLACK, 5, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 4));


        assertTrue(game.isGameover());

        game.reset();

        /*
        The following will be a representation of the board when there are no possible
        moves available for both discs when the board is not full
           A   B   C   D   E   F   G   H
        1    |   |   |   | W |   |   |
          ---+---+---+---+---+---+---+---
        2    |   |   |   | W | W |   |
          ---+---+---+---+---+---+---+---
        3  W | W | W | W | W | W | W | B
          ---+---+---+---+---+---+---+---
        4    |   | W | W | W | W |   | B
          ---+---+---+---+---+---+---+---
        5    |   | W | W | W |   |   | B
          ---+---+---+---+---+---+---+---
        6    |   |   |   |   |   |   |
          ---+---+---+---+---+---+---+---
        7    |   |   |   |   |   |   |
          ---+---+---+---+---+---+---+---
        8    |   |   |   |   |   |   |
         */

        game.doMove(new OthelloMove(Disk.BLACK, 2, 3));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 3, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 6));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 5));
        game.doMove(new OthelloMove(Disk.WHITE, 4, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 7));
        game.doMove(new OthelloMove(Disk.WHITE, 1, 5));
        game.doMove(new OthelloMove(Disk.BLACK, 3, 2));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 2));
        game.doMove(new OthelloMove(Disk.BLACK, 1, 4));
        game.doMove(new OthelloMove(Disk.WHITE, 0, 4));
        game.doMove(new OthelloMove(Disk.BLACK, 2, 1));
        game.doMove(new OthelloMove(Disk.WHITE, 3, 7));
        game.doMove(new OthelloMove(Disk.BLACK, 4, 7));
        game.doMove(new OthelloMove(Disk.WHITE, 2, 0));

        assertTrue(game.isGameover());
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
            move = player1.determineMove(game);
            game.doMove(move);
            move = player2.determineMove(game);
            game.doMove(move);
            //Since 2 turns happen in each loop, the disk color will be flipped 2 times,
            //therefore stays the same
            assertEquals(disk, game.getCurrentDisk());
        }

        assertTrue(game.isGameover());

    }

}
