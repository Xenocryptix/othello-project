package Othello.Client;

import java.net.InetAddress;

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
     *
     * @param desc description
     * @return true if success, otherwise false
     */
    boolean sendHello(String desc);

    /**
     * Send the login details to the server.
     *
     * @param username the username
     */
    void sendLogin(String username);

    /**
     * Sends a request to the server to send back the list of clients connected.
     *
     * @return true if success, otherwise false
     */
    boolean sendList();

    /**
     * Sends a request to the server to join the queue.
     *
     * @return true if success, otherwise false
     */
    void queue();

}
