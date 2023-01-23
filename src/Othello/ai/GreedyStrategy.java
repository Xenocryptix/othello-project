package Othello.ai;

import Othello.*;

import java.util.*;

public class GreedyStrategy implements Strategy {
    private static final String NAME = "GREEDY";

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
     * Return the move that flips the most disks
     *
     * @param game the game for which the move should be returned
     * @return move The move with the highest number of flips
     */
    @Override
    public Move determineMove(Game game) {
        Disk disk = ((OthelloGame) game).getCurrentDisk();
        List<Move> movesForDisk = new ArrayList<>();
        List<Move> moves = game.getValidMoves();
        for (Move currentMove : moves) {
            if (((OthelloMove) currentMove).getDisk().equals(disk)) {
                movesForDisk.add(currentMove);
            }
        }
        Map<Move,Integer> moveAndFlips = new HashMap<>();
        for (Move currentMove : movesForDisk) {
            Board board = ((OthelloGame) game).getBoard();
            int currentCount = board.countDisk(disk);
            game.doMove(currentMove);
            int newCount = board.countDisk(disk);
            moveAndFlips.put(currentMove, newCount-currentCount);
        }
        int highest = 0;
        Move highestFlippingMove = null;
        for (Move move : moveAndFlips.keySet()){
            if (moveAndFlips.get(move) > highest) {
                highest = moveAndFlips.get(move);
                highestFlippingMove = move;
            }
        }
        return highestFlippingMove;
    }
}
