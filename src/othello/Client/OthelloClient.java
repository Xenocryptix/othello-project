package othello.Client;

import othello.Server.Protocol;
import othello.model.Disk;
import othello.model.Move;
import othello.model.OthelloGame;
import othello.model.OthelloMove;
import othello.players.AbstractPlayer;
import othello.players.HumanPlayer;
import othello.players.PlayerFactory;
import othello.players.ai.GreedyStrategy;
import othello.players.ai.NaiveStrategy;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

import static othello.Server.Protocol.*;
import static othello.model.Board.DIM;

/**
 * A class representing a client who is connected to the server to play a game of Othello.
 * The class is responsible for receiving the information sent by the server and then send
 * the appropriate messages to the TUI. It is also responsible for taking the input of the
 * user from the TUI, perform appropriate checks, and then send the user input according to
 * the protocol to the server
 */
public class OthelloClient extends ClientListener implements Client, Runnable {
    private Socket client;
    private BufferedReader reader;
    private BufferedWriter writer;
    private OthelloGame game;
    private String username;
    private AbstractPlayer player;
    private AbstractPlayer opponent;
    private boolean waitingMove;
    private boolean inQueue;
    private final Listener listener;

    /**
     * Initialises the listener of the othello client to communicate with the TUI.
     *
     * @param listener The listener to be used to send messages to the TUI
     */
    public OthelloClient(Listener listener) {
        this.listener = listener;
        inQueue = false;
        waitingMove = false;
    }

    /**
     * Returns whether the player has to wait or not.
     *
     * @return true, if user has to wait, otherwise false
     */
    public boolean getStatus() {
        return waitingMove;
    }

    /**
     * Reurns the current player associated with the client.
     *
     * @return the current player
     */
    public AbstractPlayer getPlayer() {
        return player;
    }

    /**
     * Used by the TUI to allow the user to choose which kind of player the user
     * wants to be, i.e. allow a certain AI to play ot play by himself
     *
     * @param player the input by the user to select what kind of player he wants to be
     * @return true, if option chosen by the user is available, otherwise false
     */
    public boolean setPlayer(String player) {
        switch (player.toLowerCase()) {
            case "human":
                this.player = new PlayerFactory().makeHumanPlayer(username);
                break;
            case "naive":
                this.player = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
                break;
            case "greedy":
                this.player = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
                break;
            default:
                return false;
        }
        return true;
    }

    /**
     * Connect to server using the address and port number.
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
     * Close connection to a socket.
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
     * Responsible for checking if the move entered by the user is a valid move.
     * If it is, then the move is sent to the server using the protocol, otherwise,
     * an error message is sent to the user
     *
     * @param index The index at which the move is to be played
     * @return true, if the move is valid and sent to the server, otherwise false
     */
    @Override
    public boolean sendMove(int index) {
        try {
            Disk currentDisk = game.getCurrentDisk();
            int row = index / DIM;
            int col = index % DIM;
            if (index == 64 && game.getValidMoves().isEmpty() ||
                    game.isValidMove(new OthelloMove(currentDisk, row, col))) {
                writer.write(Protocol.move(index));
                writer.newLine();
                writer.flush();
                return true;
            } else if (index == 64) {
                listener.printMessage("You still have moves left");
            } else {
                listener.printMessage("Illegal move! Please input another move: ");
            }
            return false;
        } catch (IOException e) {
            System.out.println("Error occurred while sending messages");
            close();
            return false;
        }
    }

    /**
     * Responsible for sending a move to the server by an AI, if the option is chosen by the user.
     */
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


    /**
     * Send hello command to the server.
     *
     * @param description the description of the hello message
     * @return true if success, otherwise false
     */
    @Override
    public boolean sendHello(String description) {
        try {
            writer.write(Protocol.handshake(description));
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
     * Send the login details to the server, which is the username of the user.
     *
     * @param username The username of the user
     * @return True if success, otherwise false
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
     * Sends a request to the server to send back the list of clients connected.
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
     * Sends a request to the server to join the queue.
     */
    @Override
    public void queue() {
        try {
            if (player == null) {
                return;
            }
            writer.write(Protocol.queue());
            writer.newLine();
            writer.flush();
            inQueue = !inQueue;
            if (inQueue) {
                listener.printMessage("Finding match, hold tight...");
            } else {
                listener.printMessage("You've left the queue!");
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
                    case NEWGAME:
                        newgame(splitted);
                        break;
                    case GAMEOVER:
                        gameOver(splitted);
                        printMessage("");
                        break;
                    case LIST:
                        list(splitted);
                        break;
                    case ALREADYLOGGEDIN:
                        printMessage("User already logged in");
                        break;
                    case HELLO:
                        printMessage("Successfully connected to the server");
                        break;
                    case LOGIN:
                        printMessage("Logged in successfully. Have fun playing!");
                        break;
                    case MOVE:
                        move(splitted);
                        break;
                    default:
                        printMessage("Please input a valid command");
                        break;
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Checks whose turn is it. If it is the players turn then it checks whether the player
     * is playing as an AI, or human player and then does a move accordingly. IF it is not,
     * then it waits for the opponent's move.
     */
    private void checkTurn() {
        if (game.getTurn().equals(opponent)) {
            waitingMove = false;
            printMessage("Waiting for " + opponent.getName() + " to play a move...");
        } else {
            printMessage("It's your turn!");
            if (game.getTurn() instanceof HumanPlayer) {
                waitingMove = true;
            } else {
                waitingMove = true;
                sendMoveComputerPlayer();
            }
        }
    }

    /**
     * Performs a move received by the server on the game of the user and
     * prints the state of the game to the TUI after the move is performed.
     *
     * @param splitted The array including the move to be performed
     */
    private void move(String[] splitted) {
        Disk currentDisk = game.getCurrentDisk();
        int row = Integer.parseInt(splitted[1]) / DIM;
        int col = Integer.parseInt(splitted[1]) % DIM;
        game.doMove(new OthelloMove(currentDisk, row, col));
        printMessage(game.toString());
        waitingMove = false;
        checkTurn();
    }

    /**
     * Prints the list of the current players that are connected to the server
     * to the TUI.
     *
     * @param splitted The list of the players in the server
     */
    private void list(String[] splitted) {
        printMessage("Current players:");
        for (int i = 1; i < splitted.length; i++) {
            printMessage(splitted[i]);
        }
    }

    /**
     * Prints to the TUI when a game is over with the result of the game.
     *
     * @param splitted The list containing the result of the game
     */
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

    /**
     * Initialises a new game when the server adds this client to a new
     * game. It sets the players in the game according to the order they
     * are sent by the server. Meaning, the first player sent by the server
     * is the player who plays first. Then prints the state of the game, and checks
     * whose turn it is
     *
     * @param splitted The list containing the names of the players in the new game
     */
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
