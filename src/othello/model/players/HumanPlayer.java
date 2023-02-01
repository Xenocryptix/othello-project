package othello.model.players;

import othello.model.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

/**
 * Class representing a human player of the game that
 * extends an abstract class called AbstractPlayer.
 */
public class HumanPlayer extends AbstractPlayer {
    private List<Move> allowedMoves;

    /**
     * Initialised a new human player with a given name.
     *
     * @param name The name for the human player
     */
    public HumanPlayer(String name) {
        super(name);
        allowedMoves = new ArrayList<>();
    }

    public Move determineMove(Game game) {
        Scanner input = new Scanner(System.in);
        String line;
        Disk disk = ((OthelloGame) game).getCurrentDisk();
        allowedMoves.clear();
        allowedMoves = ((OthelloGame) game).getValidMoves(disk);
        if (allowedMoves.isEmpty()) {
            line = input.nextLine();
            while (!line.equals("pass")) {
                System.out.println("Check the board! Do you have a valid move?");
                line = input.nextLine();
            }
            return null;
        }
        while (true) {
            line = input.nextLine();
            int col = line.charAt(0) - 65;
            int row = line.charAt(1) - 1;
            Move move = new OthelloMove(disk, row, col);
            if (game.isValidMove(move)) {
                return move;
            }
        }
    }
}
