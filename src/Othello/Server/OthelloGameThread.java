package Othello.Server;



import Othello.model.OthelloGame;
import Othello.players.PlayerFactory;

import java.util.ArrayList;
import java.util.List;

public class OthelloGameThread implements Runnable {
    private final List<ClientHandler> players;
    private final OthelloGame game;


    public OthelloGameThread(ClientHandler player1, ClientHandler player2) {
        players = new ArrayList<>(2);
        players.add(player1);
        players.add(player2);
        String name1 = player1.getUsername();
        String name2 = player2.getUsername();
        game = new OthelloGame();
        game.setPlayer1(new PlayerFactory().makeHumanPlayer(name1));
        game.setPlayer2(new PlayerFactory().makeHumanPlayer(name2));
    }


    @Override
    public void run() {

    }
}
