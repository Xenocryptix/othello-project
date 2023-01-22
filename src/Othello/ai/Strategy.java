package Othello.ai;

import Othello.*;

public interface Strategy {
    /**
     * Return the name of the strategy
     * @return name
     */
    public String getName();

    /**
     * Return the final move
     * @param game
     * @return move
     */
    public Move determineMove(Game game);
}