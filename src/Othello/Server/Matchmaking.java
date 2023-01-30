package Othello.Server;

import Othello.Server.ClientHandler;
import Othello.Server.OthelloServer;
import Othello.Server.Server;

import java.util.List;

public class Matchmaking implements Runnable {
    private List<ClientHandler> queue;
    private OthelloServer server;
    public Matchmaking(OthelloServer server) {
        this.server = server;
    }
    @Override
    public void run() {
        while (server.isAccepting()) {
            queue = server.getQueue();
            if (server.getInQueue() >= 2) {
                server.startGame();
            }
        }
    }
}
