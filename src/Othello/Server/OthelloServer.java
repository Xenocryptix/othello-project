package Othello.Server;


import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;
import java.util.concurrent.Executor;

public class OthelloServer implements Server, Runnable {
    private final ArrayList<ClientHandler> clients;
    private final Map<ClientHandler, String> players;
    private final List<ClientHandler> playersQueue;
    private final int port;
    private final Thread serverThread;
    private ServerSocket serverSocket;
    private List<String> usernames;
    private int inQueue;

    public OthelloServer(int port) {
        this.port = port;
        clients = new ArrayList<>();
        playersQueue = new ArrayList<>();
        serverThread = new Thread(this);
        usernames = new ArrayList<>();
        players = new HashMap<>();
    }

    /**
     * Starts the server. The server should run in a separate thread,
     * so this method should return after starting this thread.
     * The server port depends on the implementation, for example,
     * the port can be given in the constructor. This method may only be run once.
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
     * Returns the port of the server.
     * This method returns the actual port the server is accepting connections on.
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
        synchronized (playersQueue) {
            playersQueue.add(handler);
            inQueue++;
        }
    }

    public void startGame() {
        synchronized (playersQueue) {
            if (playersQueue.size() >= 2) {
                ClientHandler p1 = playersQueue.remove(0);
                ClientHandler p2 = playersQueue.remove(0);
                String name1 = p1.getUsername();
                String name2 = p2.getUsername();
                p1.recieveNewGame(Protocol.newGame(name1, name2));
                p2.recieveNewGame(Protocol.newGame(name1, name2));
                ClientHandler.LOCK.notifyAll();
                OthelloGameThread game = new OthelloGameThread(p1, p2);
                new Thread(game).start();
            }
        }
    }

    public int getInQueue() {
        synchronized (playersQueue) {
            return inQueue;
        }
    }

    public List<String> getUsernames() {
        synchronized (players) {
            return new ArrayList<>(players.values());
        }
    }

    public void addUsername(String s, ClientHandler handler) {
        synchronized (players) {
            players.put(handler, s);
        }
    }

    @Override
    public void run() {
        try {
            while (isAccepting()) {
                Socket client = serverSocket.accept();
                ClientHandler handler = new ClientHandler(client, this);
                new Thread(handler).start();
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static void main(String[] args) {
        OthelloServer s = new OthelloServer(2222);
        s.start();
    }
}
