package Othello.ai;

import Othello.*;

public class ComputerPlayer extends AbstractPlayer {
    private String name;
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

    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    public Strategy getStrategy() {
        return strategy;
    }
}
