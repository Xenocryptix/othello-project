package Othello.ai;

import Othello.*;


public class NaiveStrategy implements Strategy {
    private static final String NAME = "NAIVE";

    /**
     * Return the name of the strategy
     *
     * @return name
     */
    @Override
    public String getName() {
        return NAME;
    }

    /**
     * Return the final move
     *
     * @param game
     * @return move
     */
    @Override
    public Move determineMove(Game game) {
        Disk disk = ((OthelloGame) game).getCurrentDisk();
        return ((OthelloGame) game).getRandomValidMove(disk);
    }
}
