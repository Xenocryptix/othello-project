package Othello.ai;

import Othello.Game;
import Othello.Move;

public interface Strategy {
    /**
     * Return the name of the strategy
     *
     * @return name
     */
    String getName();

    /**
     * Return the final move
     *
     * @param game
     * @return move
     */
    Move determineMove(Game game);
}