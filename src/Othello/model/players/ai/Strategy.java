package Othello.model.players.ai;

import Othello.model.Game;
import Othello.model.Move;

/**
 * A strategy to be used by the computer player.
 */
public interface Strategy {
    /**
     * Get the name of the strategy being used.
     * @return the name of the strategy used
     */
    //@ pure;
    String getName();

    /**
     * Checks the state of the game and determines the next possible move.
     * @param game The current game
     * @return the next legal move
     */
    //@ requires game != null;
    Move determineMove(Game game);
}