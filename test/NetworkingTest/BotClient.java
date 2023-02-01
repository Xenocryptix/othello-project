package NetworkingTest;

import Othello.Client.Client;
import Othello.Client.ClientListener;
import Othello.Client.Listener;
import Othello.Client.OthelloClient;
import Othello.Server.Protocol;
import Othello.model.Disk;
import Othello.model.Move;
import Othello.model.OthelloGame;
import Othello.model.OthelloMove;
import Othello.model.players.AbstractPlayer;
import Othello.model.players.PlayerFactory;
import Othello.model.players.ai.GreedyStrategy;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

import static Othello.Server.Protocol.QUEUE;
import static Othello.model.Board.DIM;

public class BotClient implements Client, Runnable {
    private final String serverAddress = "localhost";
    private final int port = 2222;
    private Socket client;
    private boolean connected = false;
    private String name;
    private boolean passed = false;
    private BufferedReader reader;
    private BufferedWriter writer;
    private OthelloGame game = new OthelloGame();
    private AbstractPlayer player;


    public BotClient(int number) {
        this.name = "BOT " + number;
        player = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
    }

    public boolean connect(InetAddress address, int port) {
        try {
            client = new Socket(address, port);
            reader = new BufferedReader(new InputStreamReader(client.getInputStream()));
            writer = new BufferedWriter(new OutputStreamWriter(client.getOutputStream()));
            new Thread(this).start();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    @Override
    public void close() {
        try {
            writer.close();
            reader.close();
            client.close();
        } catch (IOException e) {
            System.out.println("IOException");
        }
    }

    @Override
    public boolean sendMove(int index) {
        try {
            if (!game.isGameover()) {
                Disk currentDisk = game.getCurrentDisk();
                int row = index / DIM;
                int col = index % DIM;
                writer.write(Protocol.move(index));
                writer.newLine();
                writer.flush();
                return true;
            }
            return false;
        } catch (IOException e) {
            return false;
        }
    }

    public void sendMoveComputerPlayer() {
        Move move = player.determineMove(game);
        if (move == null) {
            sendMove(64);
        } else {
            int row = ((OthelloMove) move).getRow();
            int col = ((OthelloMove) move).getCol();
            int index = row * DIM + col;
            sendMove(index);
        }
    }

    public boolean sendHello(String description) {
        try {
            writer.write(Protocol.handshake(description));
            writer.newLine();
            writer.flush();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    @Override
    public void sendLogin(String username) {
        try {
            writer.write(Protocol.login(username));
            writer.newLine();
            writer.flush();
        } catch (IOException e) {
            close();
        }
    }

    @Override
    public boolean sendList() {
        return false;
    }

    @Override
    public void queue() {
        try {
            if (player == null) {
                return;
            }
            writer.write(QUEUE);
            writer.newLine();
            writer.flush();
        } catch (IOException e) {
            close();
        }
    }

    public String readReply() {
        try {
            String command = reader.readLine();
            System.out.println("[" + name + "] " + command);
            return command;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void newGame(String[] splitted) {
        game = new OthelloGame();
        AbstractPlayer opponent;
        if (splitted[1].equals(name)) {
            opponent = new PlayerFactory().makeHumanPlayer(splitted[2]);
            game.setPlayer1(player);
            game.setPlayer2(opponent);
        } else {
            opponent = new PlayerFactory().makeHumanPlayer(splitted[1]);
            game.setPlayer1(opponent);
            game.setPlayer2(player);
        }
    }

    public boolean isPassed() {
        return passed;
    }

    @Override
    public void run() {
        try {
            connected = connect(InetAddress.getByName(serverAddress), port);
        } catch (UnknownHostException e) {
            System.out.println("Failed to connect");
        }

        sendHello("TEST BOT");
        while (!readReply().contains("HELLO")) {
            System.out.println(name + " waiting for HELLO");
        }

        sendLogin(name);
        while (!readReply().contains("LOGIN")) {
            System.out.println(name + " waiting for LOGIN");
        }

        String gameData = "";
        queue();
        while (!readReply().contains("NEWGAME")) {
            System.out.println(name + " waiting for NEWGAME");
            gameData = readReply();
        }

        game = new OthelloGame();
        newGame(gameData.split("~"));
        while (!readReply().contains("GAMEOVER")) {
            if (game.getTurn().equals(player)) {
                Move move = player.determineMove(game);
                if (move == null) {
                    sendMove(64);
                } else {
                    int row = ((OthelloMove) move).getRow();
                    int col = ((OthelloMove) move).getCol();
                    int index = row * DIM + col;
                    sendMove(index);
                }
            }
        }

        passed = true;
    }
}
