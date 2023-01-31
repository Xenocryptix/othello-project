package Othello.model.players.ai;

import Othello.model.Game;
import Othello.model.Move;
import Othello.model.players.AbstractPlayer;

/**
 * Class that represents a computer player in the game.
 */
public class ComputerPlayer extends AbstractPlayer {
    private Strategy strategy;

    /**
     * Creates a new instance of the computer player and calls the super class first with the name
     * of the strategy uses.
     *
     * @param strategy The strategy to be used for the computer player
     */
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
    //@ requires game != null;
    @Override
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }

    /**
     * Returns the current strategy of the computer player.
     *
     * @return The current strategy
     */
    //@ pure
    public Strategy getStrategy() {
        return strategy;
    }

    /**
     * Updates the current strategy with a new strategy.
     *
     * @param strategy The new strategy
     */
    //@ requires strategy != null;
    //@ ensures getStrategy() == strategy;
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }
}
