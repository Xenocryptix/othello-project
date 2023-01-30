package Othello.Server;


import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;

public class OthelloServer implements Server, Runnable {
    private final Map<ClientHandler, String> players;
    private final List<OthelloGameThread> sessions;
    private final Queue<ClientHandler> playersQueue;
    private final int port;
    private final Thread serverThread;
    private final Thread matchThread;
    private ServerSocket serverSocket;


    public OthelloServer(int port) {
        this.port = port;
        playersQueue = new ArrayDeque<>();
        serverThread = new Thread(this);
        matchThread = new Thread(new Matchmaking(this));
        players = new HashMap<>();
        sessions = new ArrayList<>();
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

    public Queue<ClientHandler> getQueue() {
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
        synchronized (sessions) {
            sessions.remove(gameThread);
        }
    }

    public void startGame() {
        synchronized (playersQueue) {
            if (getInQueue() >= 2) {
                ClientHandler p1 = playersQueue.remove();
                ClientHandler p2 = playersQueue.remove();
                List<ClientHandler> pair = new ArrayList<>();
                pair.add(p1);
                pair.add(p2);

                String name1 = p1.getUsername();
                String name2 = p2.getUsername();
                p1.sendNewGame(Protocol.newGame(name1, name2));
                p2.sendNewGame(Protocol.newGame(name1, name2));

                OthelloGameThread game = new OthelloGameThread(p1, p2, this);
                sessions.add(game);
                new Thread(game).start();
            }
        }
    }

    public int getInQueue() {
        synchronized (playersQueue) {
            return playersQueue.size();
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
        if (!playersQueue.contains(handler)) {
            playersQueue.add(handler);
        } else {
            playersQueue.remove(handler);
        }
    }

    public void playMove(int index, ClientHandler clientHandler) {
        for (OthelloGameThread thread : sessions) {
            if (thread.getPlayers().contains(clientHandler)) {
                boolean moveSuccess = thread.doMove(index);
                if (!moveSuccess) {
                    clientHandler.close();
                }
            }
        }
    }
}
