package Othello.ai;

import Othello.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class NaiveStrategy implements Strategy {
    private static final String NAME = "NAIVE";
    private List<Move> allowedMoves = new ArrayList<>();
    private static final Random RANDOM = new Random();

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
        allowedMoves.clear();
        int turn = ((OthelloGame) game).getCounter();
        Disk disk;
        if (turn % 2 == 0) {
            disk = Disk.BLACK;
        } else {
            disk = Disk.WHITE;
        }
        List<Move> moves = ((OthelloGame) game).getValidMoves();
        for (Move move : moves) {
            if (((OthelloMove) move).getDisk().equals(disk)) {
                allowedMoves.add(move);
            }
        }
        int idx = RANDOM.nextInt(allowedMoves.size());
        return allowedMoves.get(idx);
    }
}
