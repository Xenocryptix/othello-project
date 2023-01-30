package Othello.exceptions;

public class UnestablishedConnection extends Exception{
    public UnestablishedConnection() {
        super("Failed to connect to this server. The server may be closed or does not exist");
    }
}
