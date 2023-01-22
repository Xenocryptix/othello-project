package Othello.ai;

import Othello.*;

public interface Factory {
    /**
     * Make a new human player
     * @param name name
     * @return human player object
     */
    HumanPlayer makeHumanPlayer(String name);

    /**
     * Make a new computer player with specified strategy
     * @param strategy
     * @return computer player object
     */
    ComputerPlayer makeComputerPlayer(Strategy strategy);
}
