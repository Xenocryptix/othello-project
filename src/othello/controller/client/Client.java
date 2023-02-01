package othello.controller.client;

import java.net.InetAddress;

/**
 * Interface which represents a general client for a game.
 */
public interface Client {
    /**
     * Connect to server using the address and port number.
     *
     * @param address host address
     * @param port    port number
     * @return true if success, otherwise false
     */
    boolean connect(InetAddress address, int port);

    /**
     * Close connection to a server.
     */
    void close();

    /**
     * Send a move to the server.
     *
     * @param index index of the move
     * @return true if success, otherwise false
     */
    boolean sendMove(int index);

    /**
     * Send hello command to the server.
     */
    void sendHello();

    /**
     * Send the login details to the server.
     *
     * @param username the username
     */
    boolean sendLogin(String username);

    /**
     * Sends a request to the server to send back the list of clients connected.
     */
    void sendList();

    /**
     * Sends a request to the server to join the queue.
     */
    void queue();

}
