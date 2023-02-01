package othello.controller.client;

import othello.controller.Protocol;
import othello.model.*;
import othello.model.players.AbstractPlayer;
import othello.model.players.HumanPlayer;
import othello.model.players.PlayerFactory;
import othello.model.players.ai.GreedyStrategy;
import othello.model.players.ai.NaiveStrategy;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import static othello.model.Board.DIM;

/**
 * A class representing a client who is connected to the server to play a game of Othello.
 * The class is responsible for receiving the information sent by the server and then send
 * the appropriate messages to the TUI. It is also responsible for taking the input of the
 * user from the TUI, perform appropriate checks, and then send the user input according to
 * the protocol to the server
 */
public class OthelloClient implements Client, Runnable {
    public static final Object LOGINLOCK = new Object();
    public static final Object CONNECTLOCK = new Object();
    public static final String SERVER_HAS_DISCONNECTED = "The server has disconnected";
    private final List<Listener> listeners;
    private Socket client;
    private BufferedReader reader;
    private BufferedWriter writer;
    private OthelloGame game;
    private String username;
    private AbstractPlayer player;
    private AbstractPlayer opponent;
    private boolean inGame;
    private boolean inQueue;
    private boolean loggedIn = false;
    private String msg;

    /**
     * Initialises the listeners of the othello client to communicate with the TUI.
     */
    public OthelloClient() {
        inQueue = false;
        inGame = false;
        listeners = new ArrayList<>();
    }

    /**
     * Adds a listener to the list of listeners to be sent to.
     *
     * @param listener The listener to be added
     */
    public void addListener(Listener listener) {
        listeners.add(listener);
    }

    /**
     * Broadcasts the message to all the listeners that are in the client.
     *
     * @param message The message to be broadcast
     */
    public void broadcast(String message) {
        for (Listener listener : listeners) {
            listener.printMessage(message);
        }
    }

    /**
     * Returns whether the user is in a game or not.
     *
     * @return true, if user is in a game, otherwise false
     */
    public boolean inGame() {
        return inGame;
    }

    /**
     * Returns the reply from the server, for debugging purposes.
     *
     * @return msg the reply
     */
    public String getMessage() {
        return msg;
    }

    /**
     * Returns the current player associated with the client.
     *
     * @return the current player
     */
    public AbstractPlayer getPlayer() {
        return player;
    }

    /**
     * Query if the user in the queue or not.
     *
     * @return true if yes, else false
     */
    public boolean isInQueue() {
        return inQueue;
    }

    /**
     * Query if the use is logged in or not.
     *
     * @return True if yes, else false
     */
    public boolean isLoggedIn() {
        return loggedIn;
    }

    /**
     * Used by the TUI to allow the user to choose which kind of player the user
     * wants to be, i.e. allow a certain AI to play ot play by himself
     *
     * @param type the input by the user to select what kind of player he wants to be
     * @return true, if option chosen by the user is available, otherwise false
     */

    public boolean setPlayer(String type) {
        switch (type.toLowerCase()) {
            case "h":
                this.player = new PlayerFactory().makeHumanPlayer(username);
                break;
            case "n":
                this.player = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
                break;
            case "g":
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
            sendHello();
            return true;
        } catch (IOException e) {
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
            broadcast("Unable to close socket");
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
            if (!game.isGameover()) {
                Disk currentDisk = game.getCurrentDisk();
                int row = index / DIM;
                int col = index % DIM;
                if (index == 64 && game.getValidMoves(game.getCurrentDisk()).isEmpty() ||
                        game.isValidMove(new OthelloMove(currentDisk, row, col))) {
                    writer.write(Protocol.move(index));
                    writer.newLine();
                    writer.flush();
                    return true;
                } else if (index == 64 && !game.getValidMoves(game.getCurrentDisk()).isEmpty()) {
                    broadcast("You still have moves left");
                }
            }
            return false;
        } catch (IOException e) {
            broadcast(SERVER_HAS_DISCONNECTED);
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
     */
    @Override
    public void sendHello() {
        try {
            writer.write(Protocol.handshake("New Client"));
            writer.newLine();
            writer.flush();
        } catch (IOException e) {
            broadcast(SERVER_HAS_DISCONNECTED);
            close();
        }
    }

    /**
     * Send the login details to the server, which is the username of the user.
     *
     * @param name The username of the user
     * @return true, if login was successfully, otherwise false
     */
    @Override
    public boolean sendLogin(String name) {
        try {
            System.out.println("Logging in...");
            this.username = name;
            if (name.contains("~")) {
                broadcast("Character \"~\" is not allowed in the username");
                return false;
            }
            writer.write(Protocol.login(name));
            writer.newLine();
            writer.flush();
            return true;
        } catch (IOException e) {
            broadcast(SERVER_HAS_DISCONNECTED);
            close();
            return false;
        }
    }

    /**
     * Sends a request to the server to send back the list of clients connected.
     */
    @Override
    public void sendList() {
        try {
            writer.write(Protocol.LIST);
            writer.newLine();
            writer.flush();
        } catch (IOException e) {
            broadcast(SERVER_HAS_DISCONNECTED);
            close();
        }
    }

    /**
     * Sends a request to the server to join the queue.
     */
    @Override
    public void queue() {
        try {
            writer.write(Protocol.QUEUE);
            writer.newLine();
            writer.flush();
            inQueue = !inQueue;
        } catch (IOException e) {
            broadcast(SERVER_HAS_DISCONNECTED);
            close();
        }
    }

    /**
     * Method which is called when a thread of OthelloClient is started which.
     * reads messages from the server and performs actions accordingly
     */
    @Override
    public void run() {
        try {
            String command;

            while ((command = reader.readLine()) != null) {
                String[] splitted = command.split(Protocol.SEPARATOR);
                msg = command;
                switch (splitted[0]) {
                    case Protocol.NEWGAME:
                        newGame(splitted);
                        break;
                    case Protocol.GAMEOVER:
                        gameOver(splitted);
                        break;
                    case Protocol.LIST:
                        list(splitted);
                        break;
                    case Protocol.ALREADYLOGGEDIN:
                        synchronized (LOGINLOCK) {
                            loggedIn = false;
                            broadcast("This user is already connected to the server. " +
                                    "Please choose a different username");
                            LOGINLOCK.notifyAll();
                        }
                        break;
                    case Protocol.HELLO:
                        synchronized (CONNECTLOCK) {
                            broadcast("Successfully connected to the server");
                            CONNECTLOCK.notifyAll();
                        }
                        break;
                    case Protocol.LOGIN:
                        synchronized (LOGINLOCK) {
                            loggedIn = true;
                            broadcast("Logged in successfully. Have fun playing!");
                            LOGINLOCK.notifyAll();
                        }
                        break;
                    case Protocol.MOVE:
                        move(splitted);
                        break;
                    default:
                        broadcast("Please input a valid command");
                        break;
                }
            }
        } catch (IOException e) {
            close();
        }
    }

    /**
     * Checks whose turn is it.
     *
     * @return true if it's your turn, otherwise false
     */
    public boolean checkTurn() {
        return game.getTurn().equals(player);
    }

    /**
     * Print the message based on current turn. If it is the players turn then
     * it checks whether the played is playing as an AI, or human player and
     * then does a move accordingly. If it is not,
     * then it waits for the opponent's move.
     */
    private void printTurn() {
        if (!checkTurn()) {
            broadcast("Waiting for " + opponent.getName() + " to play a move...");
        } else {
            if (game.getTurn() instanceof HumanPlayer) {
                broadcast("It's your turn! Enter a move below");
            } else {
                broadcast("The AI is thinking...");
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
        int index = Integer.parseInt(splitted[1]);
        if (index == 64) {
            broadcast(game.getTurn() + " has skipped");
            game.nextTurn();
        } else {
            Disk currentDisk = game.getCurrentDisk();
            int row = index / DIM;
            int col = index % DIM;
            game.doMove(new OthelloMove(currentDisk, row, col));
            broadcast(game.toString());
        }
        printTurn();
    }

    /**
     * Prints the list of the current players that are connected to the server
     * to the TUI.
     *
     * @param splitted The list of the players in the server
     */
    private void list(String[] splitted) {
        broadcast("Current players:");
        for (int i = 1; i < splitted.length; i++) {
            broadcast(splitted[i]);
        }
    }

    /**
     * Prints to the TUI when a game is over with the result of the game.
     *
     * @param splitted The list containing the result of the game
     */
    private void gameOver(String[] splitted) {
        inGame = false;
        switch (splitted[1]) {
            case Result.DISCONNECT:
                broadcast("Opponent " + opponent.getName() + " lost connection");
                break;
            case Result.DRAW:
                broadcast("You have both drawn!");
                break;
            case Result.VICTORY:
                broadcast(game.getWinner() + " won!\n");
                if (game.getWinner().toString().substring(7).equals(username)) {
                    broadcast("Congrats! you won!");
                } else {
                    broadcast("Don't worry, sometimes your opponent has a good gaming chair");
                }
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
    private void newGame(String[] splitted) {
        inQueue = false;
        inGame = true;
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
        broadcast(game.toString());
        printTurn();
    }

    /**
     * Uses the AI to produce a hint for the user if it is the user's turn,
     * and he is a human player.
     */
    public void hint() {
        if (player instanceof HumanPlayer) {
            if (checkTurn()) {
                AbstractPlayer aiHelper = new PlayerFactory().
                        makeComputerPlayer(new GreedyStrategy());
                Move move = aiHelper.determineMove(game);
                if (move == null) {
                    broadcast("No moves available to play");
                } else {
                    int row = ((OthelloMove) move).getRow() + 1;
                    char col = (char) (((OthelloMove) move).getCol() + 65);
                    broadcast("You could play a move at: " + col + row);
                }
            } else {
                broadcast("You can only use hint in your turn");
            }
        } else {
            broadcast("Bots don't need hints");
        }
    }
}