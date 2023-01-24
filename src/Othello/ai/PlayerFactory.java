package Othello.ai;

import Othello.HumanPlayer;

import java.io.Reader;
import java.io.Writer;

/**
 * A player factory used to make human players and computer players.
 */
public class PlayerFactory implements Factory {
    /**
     * Make a new human player
     *
     * @param name   name
     * @param reader reader stream
     * @param writer writer stream
     * @return human player object
     */
    @Override
    public HumanPlayer makeHumanPlayer(String name, Reader reader, Writer writer) {
        return new HumanPlayer(name, reader, writer);
    }

    /**
     * Make a new computer player with specified strategy
     *
     * @param strategy
     * @return computer player object
     */
    public ComputerPlayer makeComputerPlayer(Strategy strategy) {
        return new ComputerPlayer(strategy);
    }
}
