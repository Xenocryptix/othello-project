package Othello.ai;

import Othello.*;

import java.util.*;


public class NaiveStrategy implements Strategy {
    private static final String NAME = "NAIVE";
    private final Random rand = new Random();

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
        List<Move> validMoves = ((OthelloGame) game).getValidMoves(disk);
        if (validMoves.isEmpty()) {
            ((OthelloGame) game).nextTurn();
            return null;
        }
        return validMoves.get(rand.nextInt(validMoves.size()));
    }
}
