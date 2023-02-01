package othello.controller.server;


import othello.controller.Protocol;
import othello.model.*;
import othello.model.players.PlayerFactory;

import java.util.ArrayList;
import java.util.List;

//TODO
public class PlayingGame {
    private final List<ClientHandler> players;
    private final OthelloGame game;
    private final OthelloServer server;

    /**
     * Initiates a new game with the new client handlers.
     *
     * @param player1       The client handler of player 1
     * @param player2       The client handler of player 2
     * @param othelloServer
     */
    public PlayingGame(ClientHandler player1, ClientHandler player2, OthelloServer othelloServer) { //TODO: CAN WE REMOVE THE SERVER
        server = othelloServer;
        game = new OthelloGame();
        players = new ArrayList<>(2);
        players.add(player1);
        players.add(player2);
        String player1Name = player1.getUsername();
        String player2Name = player2.getUsername();
        game.setPlayer1(new PlayerFactory().makeHumanPlayer(player1Name));
        game.setPlayer2(new PlayerFactory().makeHumanPlayer(player2Name));
    }


    /**
     * Sends the index to both client handlers of the players.
     *
     * @param index The index to be sent
     */
    public void sendMovePlayers(int index) {
        players.get(0).sendMove(index);
        players.get(1).sendMove(index);
    }

    /**
     * Perform a move that is received from the server.
     *
     * @param index The index of the move to be made
     * @return True, if move performed correctly, otherwise, false
     */
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

    /**
     * Checks whether the came is over or not and sends a message to the client handlers
     * accordingly.
     */
    public void checkOver() {
        if (game.isGameover()) {
            String message;
            if (game.getWinner() != null) {
                message = Protocol.gameover(new String[]{Result.VICTORY, game.getWinner().toString()});
            } else {
                message = Protocol.gameover(new String[]{Result.DRAW});
            }
            players.get(0).sendMessage(message);
            players.get(1).sendMessage(message);
            server.endGame(this);
        }
    }

    /**
     * Responsible for sending the client handlers of the game the disconnected message with the
     * correct reason.
     *
     * @param clientHandler The client handler that disconnected
     */
    public void disconnect(ClientHandler clientHandler) {
        String message;
        if (clientHandler.equals(players.get(0))) {
            message = Protocol.gameover(new String[]{Result.DISCONNECT, players.get(0).getUsername()});
        } else {
            message = Protocol.gameover(new String[]{Result.DISCONNECT, players.get(1).getUsername()});
        }
        players.get(0).sendMessage(message);
        players.get(1).sendMessage(message);
    }
}
