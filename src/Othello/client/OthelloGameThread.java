package Othello.client;


import java.util.ArrayList;
import java.util.List;

public class OthelloGameThread implements Runnable {
    private final List<ClientHandler> players;


    public OthelloGameThread(ClientHandler player1, ClientHandler player2) {
        players = new ArrayList<>(2);
        players.add(player1);
        players.add(player2);
    }


    @Override
    public void run() {

    }
}
