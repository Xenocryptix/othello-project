package othello.controller.server;

import othello.controller.Protocol;
import othello.exceptions.ConnectionDropped;

import java.io.*;
import java.net.Socket;

/**
 * Class for receiving the output from the client end and communicating with the server.
 */
public class ClientHandler implements Runnable {
    private final Socket client;
    private final OthelloServer server;
    private BufferedReader reader;
    private PrintWriter writer;
    private String username;

    /**
     * Initialises a new client handler and assigns the reader and writers of
     * the socket to the local variables.
     *
     * @param client        The sockets that is passed during initialisation
     * @param othelloServer The server which this handler connected to
     */
    public ClientHandler(Socket client, OthelloServer othelloServer) {
        this.client = client;
        try {
            reader = new BufferedReader(new InputStreamReader(client.getInputStream()));
            writer = new PrintWriter(new OutputStreamWriter(client.getOutputStream()), true);
        } catch (IOException e) {
            System.out.println("Error in getting input and output streams");
        }
        this.server = othelloServer;
    }

    /**
     * Query on the username of the client handler.
     *
     * @return The username of the client handler
     */
    public String getUsername() {
        return username;
    }

    /**
     * Used to print a new game protocol message with the writer
     * to the client.
     *
     * @param newGame The protocol message
     */
    public void sendNewGame(String newGame) {
        writer.println(newGame);
    }

    /**
     * Used to close the client's reader and writers and to notify the
     * server to remove this client handler from the stored list.
     */
    public void close() {
        try {
            server.removeClient(this);
            client.close();
            writer.close();
            reader.close();
        } catch (IOException e) {
            System.out.println("Close error");
        } catch (ConnectionDropped e) {
            /*
            when a connection drop is caught, it means that the client abruptly disconnected
             */
            server.getGame(this).disconnect(this);
            System.out.println(e.getMessage());
        }
    }

    /**
     * Used to print a move protocol message with the writer
     * to the client.
     *
     * @param index The index of the move
     */
    public void sendMove(int index) {
        writer.println(Protocol.move(index));
    }

    /**
     * Used to print protocol message with the writer
     * to the client.
     *
     * @param message The message to be sent
     */
    public void sendMessage(String message) {
        writer.println(message);
    }

    /**
     * Method that is executed every time a thread is started.
     */
    @Override
    public void run() {
        try {
            String command;
            while ((command = reader.readLine()) != null) {
                String[] splitted = command.split(Protocol.SEPARATOR);
                switch (splitted[0]) {
                    case Protocol.HELLO:
                        writer.println(Protocol.handshake("Welcome to the server!"));
                        break;
                    case Protocol.LOGIN:
                        login(splitted);
                        break;
                    case Protocol.LIST:
                        writer.println(Protocol.list(server.getUsernames()));
                        break;
                    case Protocol.QUEUE:
                        queue();
                        break;
                    case Protocol.MOVE:
                        if (Integer.parseInt(splitted[1]) < 0 ||
                                Integer.parseInt(splitted[1]) > 64) {
                            close();
                        } else {
                            server.playMove(Integer.parseInt(splitted[1]), this);
                        }
                        break;
                    default:
                        writer.println(Protocol.ERROR);
                }
            }
            close();
        } catch (IOException e) {
            close();
        }
    }

    /**
     * Called when queue is sent by the client
     * and checks if this client handler is in
     * the queue or not. If yes then it removes him
     * from the queue, otherwise, it adds him
     */
    private void queue() {
        if (server.inQueue(this)) {
            server.deQueue(this);
        } else {
            server.queue(this);
        }
    }

    /**
     * Used to receive a login protocol message and check
     * if this username is used or not, if it is
     * it sends pack and ALREADYLOGGEDIN, if not
     * then it acknowledges the login and calls the server
     * to add the username.
     *
     * @param splitted The username send form the user
     */
    private void login(String[] splitted) {
        if (server.getUsernames().contains(splitted[1])) {
            writer.println(Protocol.ALREADYLOGGEDIN);
        } else {
            username = splitted[1];
            server.addUsername(splitted[1], this);
            writer.println(Protocol.LOGIN);
        }
    }
}
