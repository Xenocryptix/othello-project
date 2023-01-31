package Othello.model.players;

import Othello.model.Game;
import Othello.model.Move;

/**
 * An abstract class representing a player of the game.
 */
public abstract class AbstractPlayer implements Player {
    private final String name;

    /**
     * Creates a new Player object.
     *
     * @param name The name of the player
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Returns the name of the player.
     *
     * @return the name of the player
     */
    //@pure
    public String getName() {
        return name;
    }

    /**
     * Determines the next move, if the game still has available moves.
     *
     * @param game the current game
     * @return the player's choice
     */
    //@ requires !game.isGameover();
    //@ ensures game.isValidMove(\result);
    public abstract Move determineMove(Game game);

    /**
     * Returns a representation of a player, i.e., their name.
     *
     * @return the String representation of this object
     */
    //@ ensures \result.contains(name);
    @Override
    public String toString() {
        return "Player " + name;
    }
}
