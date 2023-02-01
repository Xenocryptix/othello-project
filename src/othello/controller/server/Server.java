package othello.controller.server;

import othello.exceptions.PortNumberException;

/**
 * Used to represent a new server instance.
 */
public interface Server {
    /**
     * Starts the server. The server should run in a separate thread,
     * so this method should return after starting this thread.
     * The server port depends on the implementation, for example,
     * the port can be given in the constructor, This method may only be run once.
     *
     * @throws PortNumberException if the port trying to use is not valid
     */
    //@ requires !isAccepting();
    //@ ensures isAccepting();
    void start() throws PortNumberException;

    /**
     * Returns the port of the server.
     * This method returns the actual port the server is accepting connections on.
     *
     * @return the port number, between 0 and 65535.
     */
    //@ ensures isAccepting() ==> \result > 0 && \result <= 65535;
    //@ pure;
    int getPort();

    /**
     * Query on if the server is currently accepting connections, and false otherwise.
     *
     * @return True if the server is accepting new connections, otherwise no
     */
    //@ pure;
    boolean isAccepting();

}
