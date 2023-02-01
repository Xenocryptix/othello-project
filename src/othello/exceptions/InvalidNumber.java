package othello.exceptions;

/**
 * Thrown when a number that is used inside a board
 * is invalid.
 */
public class InvalidNumber extends Exception {
    /**
     * Calls the super class with an error message passed.
     *
     * @param message The error message passed
     */
    public InvalidNumber(String message) {
        super(message);
    }
}
