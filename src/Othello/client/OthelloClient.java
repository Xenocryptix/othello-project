package Othello.client;

import Othello.Server.Protocol;
import Othello.model.Board;
import Othello.model.Disk;
import Othello.model.OthelloGame;
import Othello.model.OthelloMove;
import Othello.players.AbstractPlayer;
import Othello.players.PlayerFactory;
import Othello.players.ai.GreedyStrategy;
import Othello.players.ai.NaiveStrategy;

import java.io.*;
import java.net.*;

public class OthelloClient implements Client, Runnable {
    private Socket client;
    private BufferedReader reader;
    private BufferedWriter writer;
    private OthelloGame game;
    private String username;
    private AbstractPlayer player;
    private AbstractPlayer opponent;
    private boolean inGame = false;
    private boolean inQueue = false;
    private PrintWriter printWriter;
    private PipedWriter pipedWriter = new PipedWriter();

    public OthelloClient() {
        printWriter = new PrintWriter(pipedWriter, true);
    }

    public PipedWriter getPipedWriter() {
        return pipedWriter;
    }

    public boolean getStatus() {
        return inGame;
    }

    public boolean setPlayer(String player) {
        switch (player) {
            case "Human":
                this.player = new PlayerFactory().makeHumanPlayer(username);
                break;
            case "Naive":
                this.player = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
                break;
            case "Greedy":
                this.player = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
                break;
            default:
                return false;
        }
        return true;
    }
    /**
     * Connect to server using the address and port number
     *
     * @param address host address
     * @param port    port number
     * @return true if success, otherwise false
     */
    @Override
    public boolean connect(InetAddress address, int port) {
        try {
            client = new Socket(address, port);
            reader = new BufferedReader(new InputStreamReader(client.getInputStream()));
            writer = new BufferedWriter(new OutputStreamWriter(client.getOutputStream()));
            new Thread(this).start();
            return true;
        } catch (IOException e) {
            System.out.println("Failed to connect");
            return false;
        }
    }

    /**
     * Close connection to a server
     */
    @Override
    public void close() {
        try {
            writer.close();
            reader.close();
            client.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * @param index
     */
    @Override
    public boolean sendMove(int index) {
        try {
            writer.write(Protocol.move(index));
            writer.newLine();
            writer.flush();
            return true;
        } catch (IOException e) {
            System.out.println("Error occurred while sending messages");
            close();
            return false;
        }
    }

    /**
     * Send hello command to the server
     *
     * @param desc description
     * @return true if success, otherwise false
     */
    @Override
    public boolean sendHello(String desc) {
        try {
            writer.write(Protocol.handshake(desc));
            writer.newLine();
            writer.flush();
            return true;
        } catch (IOException e) {
            System.out.println("Error occurred while sending messages");
            close();
            return false;
        }
    }

    /**
     * Send the login details to the server
     *
     * @param username the username
     * @return true if success, otherwise false
     */
    @Override
    public boolean sendLogin(String username) {
        try {
            this.username = username;
            writer.write(Protocol.login(username));
            writer.newLine();
            writer.flush();
            return true;
        } catch (IOException e) {
            System.out.println("Error occurred while sending messages");
            close();
            return false;
        }
    }

    /**
     * Sends a request to the server to send back the list of clients connected
     *
     * @return true if success, otherwise false
     */
    @Override
    public boolean sendList() {
        try {
            writer.write(Protocol.LIST);
            writer.newLine();
            writer.flush();
            return true;
        } catch (IOException e) {
            System.out.println("Error occurred while sending messages");
            close();
            return false;
        }
    }

    /**
     * Sends a request to the server to join the queue
     *
     * @return true if success, otherwise false
     */
    @Override
    public void queue() {
        try {
            writer.write(Protocol.queue());
            writer.newLine();
            writer.flush();
            //TODO: change inQueue
        } catch (IOException e) {
            System.out.println("Error occurred while sending messages");
            close();
        }
    }

    @Override
    public void run() {
        try {
            String command;
            while ((command = reader.readLine()) != null) {
                String[] splitted = command.split(Protocol.SEPARATOR);
                switch (splitted[0]) {
                    case "NEWGAME":
                        game = new OthelloGame();
                        inGame = true;
                        if (splitted[1].equals(username)) {
                            opponent = new PlayerFactory().makeHumanPlayer(splitted[2]);
                            game.setPlayer1(player);
                            game.setPlayer2(opponent);
                        } else {
                            opponent = new PlayerFactory().makeHumanPlayer(splitted[1]);
                            game.setPlayer1(opponent);
                            game.setPlayer2(player);
                        }
                        break;
                    case "GAMEOVER":
                        switch (splitted[1]) {
                            case "DISCONNECT":
                                printWriter.println(splitted[2] + " disconnected");
                                break;
                            case "DRAW":
                                printWriter.println("You have both drawn!");
                                break;
                            case "VICTORY":
                                printWriter.println(splitted[2] + " won!");
                                break;
                            default:
                                throw new IllegalStateException("Unexpected value: " + splitted[1]);
                        }
                        break;
                    case "LIST":
                        printWriter.println("Current players:\n");
                        for (int i = 1; i < splitted.length; i++) {
                            printWriter.println(splitted[i] + "\n");
                        }
                        break;
                    case "ALREDYLOGGEDIN":
                        printWriter.println("User already logged in");
                        break;
                    case "HELLO":
                        printWriter.println("Successfully connected to the server");
                        break;
                    case "LOGIN":
                        printWriter.println("Logged in successfully. Have fun playing!");
                        break;
                    case "MOVE":
                        Disk currentDisk = game.getCurrentDisk();
                        int row = Integer.parseInt(splitted[1]) / Board.DIM;
                        int col = Integer.parseInt(splitted[1]) % Board.DIM;
                        game.doMove(new OthelloMove(currentDisk, row, col));
                        printWriter.println(game.toString());
                        break;
                    default:
                        printWriter.println("Invalid command");
                        break;
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
