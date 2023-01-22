package Othello;

import java.io.*;

public class HumanPlayer extends AbstractPlayer {
    String name;
    public Disk current = Disk.BLACK;
    public HumanPlayer(String name, Reader reader, Writer writer) {
        super(name);
        PrintWriter out = new PrintWriter(writer);
        BufferedReader in = new BufferedReader(reader);
    }
    public Move determineMove(Game game) {
        //TODO
        return null;
    }
    public Move getMove() {
        //TODO
        return null;
    }
}
