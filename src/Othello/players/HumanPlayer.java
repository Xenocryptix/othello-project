package Othello.players;

import Othello.model.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

/**
 * Class representing a human player of the game that
 * extends an abstract class called AbstractPlayer.
 */
public class HumanPlayer extends AbstractPlayer {
    private List<Move> allowedMoves = new ArrayList<>();


    public HumanPlayer(String name) {
        super(name);
    }

    public Move determineMove(Game game) {
        Scanner input = new Scanner(System.in);
        String line;
        Disk disk = ((OthelloGame) game).getCurrentDisk();
        allowedMoves.clear();
        allowedMoves = ((OthelloGame) game).getValidMoves(disk);
        if (allowedMoves.isEmpty()) {
            while (!(line = input.nextLine()).equals("pass")) {
                System.out.println("Check the board! Do you have a valid move?");
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
