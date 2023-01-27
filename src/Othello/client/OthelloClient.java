package Othello.client;

import Othello.Server.Protocol;
import Othello.model.*;
import Othello.players.AbstractPlayer;
import Othello.players.HumanPlayer;
import Othello.players.PlayerFactory;
import Othello.players.ai.GreedyStrategy;
import Othello.players.ai.NaiveStrategy;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

public class OthelloClient extends ClientListener implements Client, Runnable {
    private Socket client;
    private BufferedReader reader;
    private BufferedWriter writer;
    private OthelloGame game;
    private String username;
    private AbstractPlayer player;
    private AbstractPlayer opponent;
    private boolean waitingMove = false;
    private boolean inQueue = false;
    private Listener listener;
    private boolean computerPlayer = false;

    public OthelloClient(Listener listener) {
        this.listener = listener;
    }

    public boolean getStatus() {
        return waitingMove;
    }

    public AbstractPlayer getPlayer() {
        return player;
    }

    public boolean setPlayer(String player) {
        switch (player.toLowerCase()) {
            case "human":
                this.player = new PlayerFactory().makeHumanPlayer(username);
                break;
            case "naive":
                this.player = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
                computerPlayer = true;
                break;
            case "greedy":
                this.player = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
                computerPlayer = true;
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
     *
     */
    public boolean closed() {
        return client.isClosed();
    }

    public void sendMoveComputerPlayer() {
        while (!game.isGameover()) {
            Move move = player.determineMove(game);
            if (game.isValidMove(move)) {
                try {
                    int index = Integer.parseInt(Protocol.move(((OthelloMove) move).getCol() * Board.DIM) + ((OthelloMove) move).getCol());
                    game.doMove(move);
                    writer.write(index);
                    writer.newLine();
                    writer.flush();
                } catch (IOException e) {
                    e.getCause();
                }
            }
        }
    }

    /**
     * @param index
     */
    @Override
    public boolean sendMove(int index) {
        try {
            Disk currentDisk = game.getCurrentDisk();
            int row = index / Board.DIM;
            int col = index % Board.DIM;
            if ((index == 64 && game.getValidMoves().isEmpty()) || game.isValidMove(new OthelloMove(currentDisk, row, col))) {
                writer.write(Protocol.move(index));
                writer.newLine();
                writer.flush();
                return true;
            } else if (index == 64) {
                listener.printMessage("You still have moves left");
            } else {
                listener.printMessage("Illegal move, input another move");
            }
            return false;
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
            inQueue = !inQueue;
            if (inQueue) {
                listener.printMessage("Finding match...");
            } else {
                listener.printMessage("Left the queue");
            }
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
                        newgame(splitted);
                        break;
                    case "GAMEOVER":
                        gameOver(splitted);
                        break;
                    case "LIST":
                        list(splitted);
                        break;
                    case "ALREDYLOGGEDIN":
                        printMessage("User already logged in");
                        break;
                    case "HELLO":
                        printMessage("Successfully connected to the server");
                        break;
                    case "LOGIN":
                        printMessage("Logged in successfully. Have fun playing!");
                        break;
                    case "MOVE":
                        move(splitted);
                        break;
                    default:
                        printMessage("Invalid command !!");
                        break;
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void checkTurn() {
        if (game.getTurn().equals(player)) {
            printMessage("It's your turn!");
            if (game.getTurn() instanceof HumanPlayer) {
                waitingMove = true;
            }
        } else {
            printMessage("Waiting for opponent...");
            waitingMove = false;
        }
    }

    private void move(String[] splitted) {
        Disk currentDisk = game.getCurrentDisk();
        int row = Integer.parseInt(splitted[1]) / Board.DIM;
        int col = Integer.parseInt(splitted[1]) % Board.DIM;
        game.doMove(new OthelloMove(currentDisk, row, col));
        printMessage(game.toString());
        checkTurn();
    }

    private void list(String[] splitted) {
        printMessage("Current players:");
        for (int i = 1; i < splitted.length; i++) {
            printMessage(splitted[i]);
        }
    }

    private void gameOver(String[] splitted) {
        switch (splitted[1]) {
            case "DISCONNECT":
                printMessage(splitted[2] + " disconnected");
                break;
            case "DRAW":
                printMessage("You have both drawn !");
                break;
            case "VICTORY":
                printMessage(splitted[2] + " won!");
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + splitted[1]);
        }
    }

    private void newgame(String[] splitted) {
        inQueue = false;
        game = new OthelloGame();
        if (splitted[1].equals(username)) {
            opponent = new PlayerFactory().makeHumanPlayer(splitted[2]);
            game.setPlayer1(player);
            game.setPlayer2(opponent);
        } else {
            opponent = new PlayerFactory().makeHumanPlayer(splitted[1]);
            game.setPlayer1(opponent);
            game.setPlayer2(player);
        }
        listener.printMessage(game.toString());
        checkTurn();
    }
}
