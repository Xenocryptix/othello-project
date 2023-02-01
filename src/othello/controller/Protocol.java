package othello.controller;

import java.util.List;

/**
 * Protocol builder which is user by both the server and the client to be able
 * to communicate with each other.
 */
public final class Protocol {
    public static final String ERROR = "ERROR";
    public static final String HELLO = "HELLO";
    public static final String LOGIN = "LOGIN";
    public static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    public static final String LIST = "LIST";
    public static final String QUEUE = "QUEUE";
    public static final String NEWGAME = "NEWGAME";
    public static final String MOVE = "MOVE";
    public static final String GAMEOVER = "GAMEOVER";
    public static final String SEPARATOR = "~";

    /**
     * Build a new protocol description which is responsible for the handshake.
     *
     * @return the protocol description for handshake
     * @param description the description of the hello
     */
    public static String handshake(String description) {
        return HELLO + SEPARATOR + description;
    }

    /**
     * Build a new protocol message which is responsible for logging in.
     *
     * @param username The username of the client
     * @return the protocol message
     */
    public static String login(String username) {
        return LOGIN + SEPARATOR + username;
    }

    /**
     * Sent by the server to the client in respond to a LIST request.
     * Formulates message including all usernames connectes to the server
     *
     * @param usernames All names of clients connected to server
     * @return Protocol message containing all usernames in the server
     */
    public static String list(List<String> usernames) {
        String list = LIST;
        if (usernames.size() > 1) {
            for (String currentUsername : usernames) {
                list = list + SEPARATOR + currentUsername;
            }
        } else {
            list = list + SEPARATOR + usernames.get(0);
        }
        return list;
    }

    /**
     * Builds a protocol message for starting a new game from the names of two players.
     *
     * @param player1 the name of the first player to play
     * @param player2 the name of the second player to play
     * @return the protocol message to start a new game
     */
    public static String newGame(String player1, String player2) {
        return NEWGAME + SEPARATOR + player1 + SEPARATOR + player2;
    }

    /**
     * Builds a protocol message for making a move by the client.
     *
     * @param move the index of the move
     * @return the protocol message for making a move
     */
    //@ requires move >= 0 && move <= 64;
    public static String move(int move) {
        return MOVE + SEPARATOR + move;
    }

    /**
     * Builds a protocol message when a game is over for the server to be sent to the client.
     *
     * @param state the state of the game accompanied by username
     *              if there was a victory or a disconnection
     * @return the protocol message when a game is over
     */
    public static String gameover(String[] state) {
        if (state.length == 2) {
            return GAMEOVER + SEPARATOR + state[0].toUpperCase() + SEPARATOR + state[1];
        }
        return GAMEOVER + SEPARATOR + state[0].toUpperCase();
    }
}
