package othello.exceptions;

public class ConnectionDropped extends Exception {
    public ConnectionDropped(String message) {
        super(message);
    }

    @Override
    public String getMessage() {
        return super.getMessage();
    }
}
