package Othello.exceptions;

public class ServerUnavailable extends Exception{
    public ServerUnavailable() {
        super("Server is unavailable");
    }
}
