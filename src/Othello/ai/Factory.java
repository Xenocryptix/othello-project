package Othello.ai;

import Othello.*;

public interface Factory {
    /**
     * Make a new human player
     * @return human player object
     */
    HumanPlayer makeHumanPlayer();

    /**
     * Make a new computer player with specified strategy
     * @param strategy
     * @return computer player object
     */
    ComputerPlayer makeComputerPlayer(Strategy strategy);
}
