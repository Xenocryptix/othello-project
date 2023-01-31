package Othello.Server;


public class Matchmaking implements Runnable {
    private final OthelloServer server;
    public Matchmaking(OthelloServer server) {
        this.server = server;
    }
    @Override
    public void run() {
        while (server.isAccepting()) {
            if (server.getInQueue() >= 2) {
                server.startGame();
            }
        }
    }
}
