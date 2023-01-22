package Othello.ai;

import Othello.Player;

public interface Strategy {
    /**
     * Make a new human player
     * @return human player object
     */
    Player makeHumanPlayer();

    /**
     * Make a new computer player with specified strategy
     * @param strategy
     * @return computer player object
     */
    Player makeComputerPlayer(Strategy strategy);
}