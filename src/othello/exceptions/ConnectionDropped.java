package othello.exceptions;

/**
 * Thrown when a connection between a client and a server
 * is dropped.
 */
public class ConnectionDropped extends Exception {
    /**
     * Calls the super class with the error message
     * passed as a parameter.
     *
     * @param message The error message passed
     */
    public ConnectionDropped(String message) {
        super(message);
    }

}
