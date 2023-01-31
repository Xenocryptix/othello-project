package Othello.model.players.ai;

import Othello.model.Disk;
import Othello.model.Game;
import Othello.model.Move;
import Othello.model.OthelloGame;

import java.util.List;
import java.util.Random;

/**
 * A naive strategy for the othello game which picks a move randomly from the valid moves.
 */
public class NaiveStrategy implements Strategy {
    /**
     * Creates a new instance of NaiveStrategy.
     */
    public NaiveStrategy() {

    }
    private static final String NAME = "NAIVE";
    private final Random rand = new Random();

    /**
     * Get the name of the strategy being used.
     * @return the name of the strategy used
     */
    //@ ensures \result == NAME;
    @Override
    public String getName() {
        return NAME;
    }

    /**
     * Checks the state of the game and determines the next possible random move.
     * @param game The current game
     * @return the next legal move
     */
    //@ requires game != null;
    //@ ensures ((OthelloGame) game).isValidMove(\result);
    @Override
    public Move determineMove(Game game) {
        Disk disk = ((OthelloGame) game).getCurrentDisk();
        List<Move> validMoves = ((OthelloGame) game).getValidMoves(disk);
        if (validMoves.isEmpty()) {
            return null;
        }
        return validMoves.get(rand.nextInt(validMoves.size()));
    }
}
