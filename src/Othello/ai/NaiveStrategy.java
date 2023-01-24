package Othello.ai;

import Othello.Disk;
import Othello.Game;
import Othello.Move;
import Othello.OthelloGame;

import java.util.List;
import java.util.Random;


public class NaiveStrategy implements Strategy {
    private static final String NAME = "NAIVE";
    private final Random RAND = new Random();

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
        return validMoves.get(RAND.nextInt(validMoves.size()));
    }
}
