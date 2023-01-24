package Othello.players.ai;

import Othello.players.AbstractPlayer;
import Othello.model.Game;
import Othello.model.Move;
import Othello.players.Strategy;

/**
 * Class that represents a computer player in the game
 */
public class ComputerPlayer extends AbstractPlayer {
    private Strategy strategy;

    public ComputerPlayer(Strategy strategy) {
        super(strategy.getName());
        this.strategy = strategy;
    }

    /**
     * Determines the next move, if the game still has available moves.
     *
     * @param game the current game
     * @return the player's choice
     */
    @Override
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }

    /**
     * Returns the current strategy of the computer player
     *
     * @return The current strategy
     */
    //@ pure
    public Strategy getStrategy() {
        return strategy;
    }

    /**
     * Updates the current strategy with a new strategy
     *
     * @param strategy The new strategy
     */
    //@ requires strategy != null;
    //@ ensures getStrategy() == strategy;
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }
}
