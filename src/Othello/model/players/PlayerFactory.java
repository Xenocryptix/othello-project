package Othello.model.players;

import Othello.model.players.ai.Strategy;
import Othello.model.players.ai.ComputerPlayer;

/**
 * A player factory used to make human players and computer players.
 */
public class PlayerFactory implements Factory {
    /**
     * Creates a new instance of PlayerFactory.
     */
    public PlayerFactory() {
    }

    /**
     * Make a new human player.
     *
     * @param name name The name of the human player
     * @return The human player object
     */
    //@ requires name != null;
    @Override
    public HumanPlayer makeHumanPlayer(String name) {
        return new HumanPlayer(name);
    }

    /**
     * Make a new computer player with specified strategy.
     *
     * @param strategy The strategy to be used
     * @return The computer player object
     */
    //@ requires strategy != null;
    public ComputerPlayer makeComputerPlayer(Strategy strategy) {
        return new ComputerPlayer(strategy);
    }
}
