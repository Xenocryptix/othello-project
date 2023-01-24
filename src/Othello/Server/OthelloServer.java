package Othello.Server;

import Othello.client.ClientHandler;
import Othello.client.OthelloGameThread;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.PriorityQueue;
import java.util.Queue;

public class OthelloServer implements Server, Runnable {
    private final ArrayList<ClientHandler> clients;
    private final Queue<ClientHandler> playersQueue;
    private final int port;
    private final Thread serverThread;
    private ServerSocket serverSocket;

    public OthelloServer(int port) {
        this.port = port;
        clients = new ArrayList<ClientHandler>();
        playersQueue = new PriorityQueue<>();
        serverThread = new Thread(this);
    }

    /**
     * Starts the server. The server should run in a separate thread, so this method should return after starting this
     * thread. The server port depends on the implementation, for example, the port can be given in the constructor.
     * This method may only be run once.
     */
    @Override
    public void start() {
        try {
            serverSocket = new ServerSocket(port);
            serverThread.start();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

    /**
     * Returns the port of the server. This method returns the actual port the server is accepting connections on.
     *
     * @return the port number, between 0 and 65535.
     */
    @Override
    public int getPort() {
        return serverSocket.getLocalPort();
    }

    /**
     * Stops the server. This method returns after the server thread has actually stopped.
     * This method may only be run once and only after start() has been called before.
     */
    @Override
    public void stop() {
        try {
            serverSocket.close();
            serverThread.join();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.getCause();
        }
    }

    /**
     * Returns true if the server is currently accepting connections, and false otherwise.
     */
    @Override
    public boolean isAccepting() {
        return serverThread.isAlive();
    }


    public synchronized void addClient(ClientHandler handler) {
        clients.add(handler);
    }

    public void addToQueue(ClientHandler handler) {
        playersQueue.add(handler);
    }


    @Override
    public void run() {
        try {
            while (isAccepting()) {
                Socket client = serverSocket.accept();
                ClientHandler handler = new ClientHandler(client, this);
                addClient(handler);
                new Thread(handler).start();
                if (playersQueue.size() >= 2) {
                    OthelloGameThread game = new OthelloGameThread(playersQueue.remove(), playersQueue.remove());
                    new Thread(game).start();
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }


}
