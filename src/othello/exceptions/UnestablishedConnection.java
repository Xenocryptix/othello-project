package othello.exceptions;

public class UnestablishedConnection extends Exception{
    public UnestablishedConnection(String message) {
        super(message);
    }

    @Override
    public String getMessage() {
        return super.getMessage();
    }
}
