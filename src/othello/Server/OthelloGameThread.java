package othello.Server;


import othello.model.Board;
import othello.model.Disk;
import othello.model.OthelloGame;
import othello.model.OthelloMove;
import othello.players.HumanPlayer;
import othello.players.PlayerFactory;

import java.util.ArrayList;
import java.util.List;

public class OthelloGameThread implements Runnable {
    private final List<ClientHandler> players;
    private final OthelloGame game;
    private final String player1Name;
    private final String player2Name;


    public OthelloGameThread(ClientHandler player1, ClientHandler player2) {
        players = new ArrayList<>(2);
        players.add(player1);
        players.add(player2);
        player1Name = player1.getUsername();
        player2Name = player2.getUsername();
        game = new OthelloGame();
        game.setPlayer1(new PlayerFactory().makeHumanPlayer(player1Name));
        game.setPlayer2(new PlayerFactory().makeHumanPlayer(player2Name));
    }

    public ClientHandler getTrun() {
        if (((HumanPlayer) game.getTurn()).getName().equals(player1Name)) {
            return players.get(0);
        } else {
            return players.get(1);
        }
    }

    @Override
    public void run() {
        while (!game.isGameover()) {
            int row;
            int col;
            if (getTrun().equals(players.get(0))) {
                row = players.get(0).getCurrentIndex() / Board.DIM;
                col = players.get(0).getCurrentIndex() % Board.DIM;
                game.doMove(new OthelloMove(Disk.BLACK, row, col));
                players.get(1).setMove(players.get(0).getCurrentIndex());
            } else {
                row = players.get(1).getCurrentIndex() / Board.DIM;
                col = players.get(1).getCurrentIndex() % Board.DIM;
                game.doMove(new OthelloMove(Disk.WHITE, row, col));
                players.get(0).setMove(players.get(1).getCurrentIndex());
            }
        }
    }
}
