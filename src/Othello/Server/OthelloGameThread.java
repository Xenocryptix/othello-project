package Othello.Server;


import Othello.model.Board;
import Othello.model.Disk;
import Othello.model.OthelloGame;
import Othello.model.OthelloMove;
import Othello.players.PlayerFactory;

import java.util.ArrayList;
import java.util.List;

public class OthelloGameThread implements Runnable {
    private final List<ClientHandler> players;
    private final String player1Name;
    private final String player2Name;
    private final OthelloGame game;


    public OthelloGameThread(ClientHandler player1, ClientHandler player2) {
        game = new OthelloGame();
        players = new ArrayList<>(2);
        players.add(player1);
        players.add(player2);
        player1Name = player1.getUsername();
        player2Name = player2.getUsername();
        game.setPlayer1(new PlayerFactory().makeHumanPlayer(player1Name));
        game.setPlayer2(new PlayerFactory().makeHumanPlayer(player2Name));
    }

    public List<ClientHandler> getPlayers() {
        return players;
    }

    @Override
    public void run() {

    }

    public void sendMovePlayers(int index) {
        players.get(0).sendMove(index);
        players.get(1).sendMove(index);
    }

    public boolean doMove(int index) {
        synchronized (game) {
            int row = index / Board.DIM;
            int col = index % Board.DIM;
            Disk disk = game.getCurrentDisk();
            if (index == 64 && game.getValidMoves(disk).isEmpty()) {
                sendMovePlayers(index);
                game.nextTurn();
                checkOver();
                return true;
            } else if (game.isValidMove(new OthelloMove(disk, row, col))) {
                sendMovePlayers(index);
                game.doMove(new OthelloMove(game.getCurrentDisk(), row, col));
                checkOver();
                return true;
            } else {
                return false;
            }
        }
    }

    public boolean checkOver() {
        if (game.isGameover()) {
            String message;
            if (game.getWinner() != null) {
                message = Protocol.gameover(new String[]{"VICTORY", game.getWinner().toString()});
            } else {
                message = Protocol.gameover(new String[]{"DRAW"});
            }
            players.get(0).sendMessage(message);
            players.get(1).sendMessage(message);
            return true;
        }
        return false;
    }
}
