package othello.exceptions;

public class PortNumberException extends Exception {
    public PortNumberException() {
        super("The specified port is invalid or unavailable");
    }
}
