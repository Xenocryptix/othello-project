package Othello;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

/**
 * Class representing a human player of the game that extends an abstract class called AbstractPlayer.
 * //TODO
 */
public class HumanPlayer extends AbstractPlayer {
    private final PrintWriter out;
    private final BufferedReader in;
    private List<Move> allowedMoves = new ArrayList<>();

    public HumanPlayer(String name, Reader reader, Writer writer) {
        super(name);
        out = new PrintWriter(writer, true);
        in = new BufferedReader(reader);
    }

    public Move determineMove(Game game) {
        Disk disk = ((OthelloGame) game).getCurrentDisk();
        allowedMoves.clear();
        allowedMoves = ((OthelloGame) game).getValidMoves(disk);

        try {
            while (true) {
                String line = in.readLine();
                String[] split = line.split("~");
                if (!line.contains("MOVE~") || split.length < 2) {
                    out.write("Invalid format");
                    continue;
                }
                int row = split[1].charAt(0) - 65;
                int col = split[1].charAt(1);
                Move move = new OthelloMove(disk, row, col);
                if (game.isValidMove(move)) {
                    return move;
                }
                out.write("Illegal move");
            }
        } catch (IOException e) {
            out.write("Invalid format");
        }
        return null;
    }
}
