package Othello.ai;

import Othello.*;

import java.util.*;

public class SmartStrategy implements Strategy {
    /**
     * Return the name of the strategy
     *
     * @return name
     */
    @Override
    public String getName() {
        return null;
    }

    /**
     * Return the move that flips the most disks
     *
     * @param game
     * @return move
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
            game.doMove(currentMove);;
            int newCount = board.countDisk(disk);
            moveAndFlips.put(currentMove, newCount-currentCount);
        }
        //TODO: SORT AND GET THE HIGHEST FLIPS
    }
}
