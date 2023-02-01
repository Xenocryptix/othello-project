package GameLogicTest;

import org.junit.jupiter.api.Test;
import othello.model.Disk;
import othello.model.OthelloGame;
import othello.model.players.AbstractPlayer;
import othello.model.players.PlayerFactory;
import othello.model.players.ai.GreedyStrategy;
import othello.model.players.ai.NaiveStrategy;
import org.junit.jupiter.api.BeforeEach;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Responsible for testing the two different AI's developed
 */
public class AITests {
    private OthelloGame game;

    @BeforeEach
    public void setUp() {
        game = new OthelloGame();
    }

    @Test
    public void fullRandomGame() {
        int naiveWinner = 0;
        int greedyWinner = 0;
        assertFalse(game.isGameover());
        AbstractPlayer player1 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        AbstractPlayer player2 = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
        game.setPlayer1(player1);
        game.setPlayer2(player2);
        for (int i = 0; i < 1000; i++) {
            //Allows both players to make moves while the game is not over
            //Get the disk of the current turn
            Disk disk = game.getCurrentDisk();
            while (!game.isGameover()) {
                game.doMove(player1.determineMove(game));
                game.doMove(player2.determineMove(game));
                //Since 2 turns happen in each loop, the disk color will be flipped 2 times,
                //therefore stays the same
                assertEquals(disk, game.getCurrentDisk());
            }
            assertTrue(game.isGameover());
            if (game.getWinner() == player1) {
                naiveWinner++;
            } else if (game.getWinner() == player2) {
                greedyWinner++;
            }
            game.reset();
        }
        assertTrue(greedyWinner > naiveWinner);
    }
}


