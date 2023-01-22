package Othello.ai;

public interface Strategy {
    /**
     * Make a new human player
     * @return human player object
     */
    void makeHumanPlayer();

    /**
     * Make a new computer player with specified strategy
     * @param strategy
     * @return computer player object
     */
    void makeComputerPlayer(Strategy strategy);
}