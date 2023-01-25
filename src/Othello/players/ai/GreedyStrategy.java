package Othello.players.ai;

import Othello.model.*;

import java.util.List;

/**
 * Represents a greedy strategy that picks the move that flips the most disks
 */
public class GreedyStrategy implements Strategy {
    /**
     * Creates a new instance of GreedyStrategy
     */
    public GreedyStrategy(){}
    private static final String NAME = "GREEDY";

    /**
     * Return the name of the strategy
     *
     * @return name
     */
    //@ ensures \result == NAME;
    @Override
    public String getName() {
        return NAME;
    }

    /**
     * Return the move that flips the most disks
     *
     * @param game The game for which the move should be returned
     * @return move The move with the highest number of flips
     */
    //@ requires game != null;
    //@ ensures ((OthelloGame) game).isValidMove(\result);
    @Override
    public Move determineMove(Game game) {
        Disk disk = ((OthelloGame) game).getCurrentDisk();
        List<Move> movesForDisk;
        movesForDisk = ((OthelloGame) game).getValidMoves(disk);
        if (movesForDisk.isEmpty())
            return null;
        Move highestMove = movesForDisk.get(0);
        int highestFlips = 0;

        for (Move currentMove : movesForDisk) {
            Board board = ((OthelloGame) game).deepCopy();
            int currentCount = board.countDisk(disk);
            board.flipMove(currentMove);
            int flips = board.countDisk(disk) - currentCount;

            if (flips >= highestFlips) {
                highestMove = currentMove;
                highestFlips = flips;
            }
        }

        return highestMove;
    }
}
