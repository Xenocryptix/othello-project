package Othello.players.ai;

import Othello.*;
import Othello.players.Strategy;

import java.util.List;

public class GreedyStrategy implements Strategy {
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
            return new OthelloMove(disk, 8, 0);

        Move highestMove = movesForDisk.get(0);
        int highestFlips = 0;

        for (Move currentMove : movesForDisk) {
            Board board = ((OthelloGame) game).getBoard().deepCopy();
            OthelloGame newGame = new OthelloGame();
            newGame.setBoard(board);
            int currentCount = newGame.getBoard().countDisk(disk);
            newGame.doMove(currentMove);
            int flips = newGame.getBoard().countDisk(disk) - currentCount;

            if (flips >= highestFlips) {
                highestMove = currentMove;
                highestFlips = flips;
            }
        }

        return highestMove;
    }
}
