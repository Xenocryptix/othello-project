package Othello.players;

import Othello.players.ai.ComputerPlayer;

import java.io.Reader;
import java.io.Writer;

/**
 * Interface factory for creating players.
 */

public interface Factory {
    /**
     * Make a new human player
     *
     * @param name   name
     * @param reader reader stream
     * @param writer writer stream
     * @return human player object
     */
    //@ requires name != null && reader != null && writer != null;
    HumanPlayer makeHumanPlayer(String name, Reader reader, Writer writer);

    /**
     * Make a new computer player with specified strategy
     *
     * @param strategy strategy
     * @return computer player object
     */
    //@ requires strategy != null;
    ComputerPlayer makeComputerPlayer(Strategy strategy);
}
