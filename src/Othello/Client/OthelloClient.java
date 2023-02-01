package Othello.Client;

import Othello.Server.Protocol;
import Othello.model.Disk;
import Othello.model.Move;
import Othello.model.OthelloGame;
import Othello.model.OthelloMove;
import Othello.model.players.AbstractPlayer;
import Othello.model.players.HumanPlayer;
import Othello.model.players.PlayerFactory;
import Othello.model.players.ai.GreedyStrategy;
import Othello.model.players.ai.NaiveStrategy;


import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

import static Othello.Server.Protocol.*;
import static Othello.model.Board.DIM;

/**
 * A class representing a client who is connected to the server to play a game of Othello.
 * The class is responsible for receiving the information sent by the server and then send
 * the appropriate messages to the TUI. It is also responsible for taking the input of the
 * user from the TUI, perform appropriate checks, and then send the user input according to
 * the protocol to the server
 */
public class OthelloClient implements Client, Runnable {
    private final ClientListener clientListener = new ClientListener();
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
    private Listener listener;
    public static final Object LOGINLOCK = new Object();
    public static final Object CONNECTLOCK = new Object();
    private String msg;

    /**
     * Initialises the listener of the othello client to communicate with the TUI.
     *
     * @param listener The listener to be used to send messages to the TUI
     */
    public OthelloClient(Listener listener) {
        this.listener = listener;
        inQueue = false;
        inGame = false;
    }

    public OthelloClient() {
        inQueue = false;
        inGame = false;
    }

    /**
     * Returns whether the user is in a game or not
     *
     * @return true, if user is in a game, otherwise false
     */
    public boolean inGame() {
        return inGame;
    }

    /**
     * Returns the reply from the server, for debugging purposes
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

    public boolean isLoggedIn() {
        return loggedIn;
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
            //TODO: MESSAGE
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
                    listener.printMessage("You still have moves left");
                }
            }
            return false;
        } catch (IOException e) {
            clientListener.printMessage("The server has disconnected");
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
            clientListener.printMessage("The server has disconnected");
            close();
            return false;
        }
    }

    /**
     * Send the login details to the server, which is the username of the user.
     *
     * @param username The username of the user
     * @return
     */
    @Override
    public boolean sendLogin(String username) {
        try {
            System.out.println("Logging in...");
            this.username = username;
            if (username.contains("~")) {
                clientListener.printMessage("Character \"~\" is not allowed in the username");
                return false;
            }
            writer.write(Protocol.login(username));
            writer.newLine();
            writer.flush();
            return true;
        } catch (IOException e) {
            clientListener.printMessage("The server has disconnected");
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
            clientListener.printMessage("The server has disconnected");
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
            writer.write(QUEUE);
            writer.newLine();
            writer.flush();
            inQueue = !inQueue;
        } catch (IOException e) {
            clientListener.printMessage("The server has disconnected");
            close();
        }
    }

    @Override
    public void run() {
        try {
            String command;

            while ((command = reader.readLine()) != null) {
                String[] splitted = command.split(SEPARATOR);
                msg = splitted[0];
                switch (splitted[0]) {
                    case NEWGAME:
                        newGame(splitted);
                        break;
                    case GAMEOVER:
                        gameOver(splitted);
                        break;
                    case LIST:
                        list(splitted);
                        break;
                    case ALREADYLOGGEDIN:
                        synchronized (LOGINLOCK) {
                            loggedIn = false;
                            clientListener.printMessage("This user is already connected to the server. Please choose a different username");
                            LOGINLOCK.notifyAll();
                        }
                        break;
                    case HELLO:
                        synchronized (CONNECTLOCK) {
                            clientListener.printMessage("Successfully connected to the server");
                            CONNECTLOCK.notifyAll();
                        }
                        break;
                    case LOGIN:
                        synchronized (LOGINLOCK) {
                            loggedIn = true;
                            clientListener.printMessage("Logged in successfully. Have fun playing!");
                            LOGINLOCK.notifyAll();
                        }
                        break;
                    case MOVE:
                        move(splitted);
                        break;
                    default:
                        clientListener.printMessage("Please input a valid command");
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
     * Print the message based on current turn. If it is the players turn then it checks whether the player
     * is playing as an AI, or human player and then does a move accordingly. IF it is not,
     * then it waits for the opponent's move.
     */
    private void printTurn() {
        if (!checkTurn()) {
            clientListener.printMessage("Waiting for " + opponent.getName() + " to play a move...");
        } else {
            if (game.getTurn() instanceof HumanPlayer) {
                clientListener.printMessage("It's your turn! Enter a move below");
            } else {
                clientListener.printMessage("The AI is thinking...");
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
            clientListener.printMessage(game.getTurn() + " has skipped");
            game.nextTurn();
        } else {
            Disk currentDisk = game.getCurrentDisk();
            int row = index / DIM;
            int col = index % DIM;
            game.doMove(new OthelloMove(currentDisk, row, col));
            clientListener.printMessage(game.toString());
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
        clientListener.printMessage("Current players:");
        for (int i = 1; i < splitted.length; i++) {
            clientListener.printMessage(splitted[i]);
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
            case "DISCONNECT":
                clientListener.printMessage("Opponent " + opponent.getName() + " lost connection");
                break;
            case "DRAW":
                clientListener.printMessage("You have both drawn!");
                break;
            case "VICTORY":
                clientListener.printMessage(game.getWinner() + " won!\n");
                if (game.getWinner().toString().substring(7).equals(username)) {
                    clientListener.printMessage("Congrats! you won!");
                } else {
                    clientListener.printMessage("Don't worry, sometimes your opponent has a good gaming chair");
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
        listener.printMessage(game.toString());
        printTurn();
    }

    /**
     * Uses the AI to produce a hint for the user if it is the user's turn,
     * and he is a human player.
     */
    public void hint() {
        if (player instanceof HumanPlayer) {
            if (checkTurn()) {
                AbstractPlayer aiHelper = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
                Move move = aiHelper.determineMove(game);
                if (move == null) {
                    clientListener.printMessage("No moves available to play");
                } else {
                    int row = ((OthelloMove) move).getRow() + 1;
                    char col = (char) (((OthelloMove) move).getCol() + 65);
                    clientListener.printMessage("You could play a move at: " + col + row);
                }
            } else {
                clientListener.printMessage("You can only use hint in your turn");
            }
        } else {
            clientListener.printMessage("Bots don't need hints");
        }
    }
}