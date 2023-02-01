package othello.exceptions;

/**
 * Thrown when trying to connect to a port number but
 * it is not available.
 */
public class PortNumberException extends Exception {
    /**
     * Calls the super class with the error message.
     */
    public PortNumberException() {
        super("The specified port is invalid or unavailable");
    }
}
