package Othello.ai;

import Othello.*;

public class PlayerFactory implements Factory {
    /**
     * Make a new human player
     * @return human player object
     */
    public HumanPlayer makeHumanPlayer() {
        return new HumanPlayer();
    }

    /**
     * Make a new computer player with specified strategy
     * @param strategy
     * @return computer player object
     */
    public ComputerPlayer makeComputerPlayer(Strategy strategy) {
        return new ComputerPlayer(strategy);
    }
}
