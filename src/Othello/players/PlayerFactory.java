package Othello.players;

import Othello.players.Factory;
import Othello.players.HumanPlayer;
import Othello.players.Strategy;
import Othello.players.ai.ComputerPlayer;

import java.io.Reader;
import java.io.Writer;

/**
 * A player factory used to make human players and computer players.
 */
public class PlayerFactory implements Factory {
    /**
     * Make a new human player
     *
     * @param name   name The name of the human player
     * @param reader The reader stream of the socket
     * @param writer The writer stream of the socket
     * @return The human player object
     */
    //@ requires name != null && reader != null && writer != null;
    @Override
    public HumanPlayer makeHumanPlayer(String name, Reader reader, Writer writer) {
        return new HumanPlayer(name, reader, writer);
    }

    /**
     * Make a new computer player with specified strategy
     *
     * @param strategy The strategy to be used
     * @return The computer player object
     */
    //@ requires strategy != null;
    public ComputerPlayer makeComputerPlayer(Strategy strategy) {
        return new ComputerPlayer(strategy);
    }
}
