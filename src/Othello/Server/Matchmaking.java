package Othello.Server;

import java.util.List;
import java.util.Queue;

public class Matchmaking implements Runnable {
    private final OthelloServer server;
    public Matchmaking(OthelloServer server) {
        this.server = server;
    }
    @Override
    public void run() {
        while (server.isAccepting()) {
            List<ClientHandler> queue = server.getQueue();
            if (server.getInQueue() >= 2) {
                server.startGame();
            }
        }
    }
}