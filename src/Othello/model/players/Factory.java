package Othello.model.players;

import Othello.model.players.ai.Strategy;
import Othello.model.players.ai.ComputerPlayer;

/**
 * Interface factory for creating players.
 */

public interface Factory {
    /**
     * Make a new human player.
     *
     * @param name   name
     * @return human player object
     */
    //@ requires name != null;
    HumanPlayer makeHumanPlayer(String name);

    /**
     * Make a new computer player with specified strategy.
     *
     * @param strategy strategy
     * @return computer player object
     */
    //@ requires strategy != null;
    ComputerPlayer makeComputerPlayer(Strategy strategy);
}
