package Othello.Server;


import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;

public class OthelloServer implements Server, Runnable {
    private final Map<ClientHandler, String> players;
    private final Map<List<ClientHandler>, OthelloGameThread> sessions;
    private final List<ClientHandler> playersQueue;
    private final int port;
    private final Thread serverThread;
    private final Thread matchThread;
    private ServerSocket serverSocket;
    private int inQueue;


    public OthelloServer(int port) {
        this.port = port;
        playersQueue = new ArrayList<>();
        serverThread = new Thread(this);
        matchThread = new Thread(new Matchmaking(this));
        players = new HashMap<>();
        sessions = new HashMap<>();
        inQueue = 0;
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
            matchThread.start();
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

    public List<ClientHandler> getQueue() {
        return playersQueue;
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

    @Override
    public void run() {
        try {
            while (isAccepting()) {
                Socket client = serverSocket.accept();
                ClientHandler handler = new ClientHandler(client, this);
                addClient(handler);
                new Thread(handler).start();
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public void addClient(ClientHandler handler) {
        synchronized (players) {
            players.put(handler, handler.getUsername());
        }
    }

    public void removeClient(ClientHandler handler) {
        synchronized (players) {
            players.remove(handler);
        }
    }

    public void endGame(OthelloGameThread gameThread) {
        for (List<ClientHandler> ch : sessions.keySet()) {
            if (sessions.get(ch).equals(gameThread)) {
                sessions.remove(ch);
                inQueue = inQueue - 2;
            }
        }
    }

    public void startGame() {
        synchronized (playersQueue) {
            if (getInQueue() >= 2) {
                ClientHandler p1 = playersQueue.remove(0);
                ClientHandler p2 = playersQueue.remove(0);
                List<ClientHandler> players = new ArrayList<>();
                players.add(p1);
                players.add(p2);

                String name1 = p1.getUsername();
                String name2 = p2.getUsername();
                p1.recieveNewGame(Protocol.newGame(name1, name2));
                p2.recieveNewGame(Protocol.newGame(name1, name2));

                OthelloGameThread game = new OthelloGameThread(p1, p2, this);
                sessions.put(players, game);
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

    public static void main(String[] args) {
        OthelloServer s = new OthelloServer(2222);
        s.start();
    }

    public void queue(ClientHandler handler) {
        synchronized (playersQueue) {
            if (!playersQueue.contains(handler)) {
                playersQueue.add(handler);
                inQueue++;
            } else {
                playersQueue.remove(handler);
                inQueue--;
            }
        }
    }

    public void playMove(int index, ClientHandler clientHandler) {
        for (List<ClientHandler> ch : sessions.keySet()) {
            if (ch.contains(clientHandler)) {
                OthelloGameThread currentGame = sessions.get(ch);
                if (!currentGame.doMove(index)) {
                    clientHandler.close();
                }
            }
        }
    }
}
