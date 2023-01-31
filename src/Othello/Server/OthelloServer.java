package Othello.Server;


import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

//TODO
public class OthelloServer implements Server, Runnable {
    private final Map<ClientHandler, String> players;
    private final Map<List<ClientHandler>, GameThread> sessions;
    private final List<ClientHandler> playersQueue;
    private final int port;
    private final Thread serverThread;
    private final Thread matchThread;
    private ServerSocket serverSocket;


    public OthelloServer(int port) {
        this.port = port;
        playersQueue = new ArrayList<>();
        serverThread = new Thread(this);
        matchThread = new Thread(new Matchmaking(this));
        players = new HashMap<>();
        sessions = new HashMap<>();
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
            System.out.println("Couldn't start the server");
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
     * Query on the players that are in the queue
     *
     * @return The list of client handlers that are in queue
     */
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
            //TODO:MESSAGE
        } catch (InterruptedException e) {
            //TODO:MESSAGE
        }
    }

    /**
     * Returns true if the server is currently accepting connections, and false otherwise.
     */
    @Override
    public boolean isAccepting() {
        return serverThread.isAlive();
    }

    /**
     * The run method that runs while the server is not closed and accepts new clients
     * and adds them to the client handler list and start a new thread for that client
     */
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
            //TODO: MESSAGE
        }
    }

    /**
     * Adds a client handler with their username to a list stored
     * in the server called players to store all the players
     * in the game.
     *
     * @param clientHandler The client handler to be added to players
     */
    public void addClient(ClientHandler clientHandler) {
        synchronized (players) {
            players.put(clientHandler, clientHandler.getUsername());
        }
    }

    /**
     * When a client abruptly disconnects, this method is called
     * to remove this player from the server as well as ensure that
     * the player is removed from the queue.
     *
     * @param clientHandler The client handler that disconnected
     */
    public void removeClient(ClientHandler clientHandler) {
        synchronized (players) {
            players.remove(clientHandler);
            playersQueue.remove(clientHandler);
        }
    }

    /**
     * Ends a session of a game when the game is over from the GameThread
     * class.
     *
     * @param gameThread The game that is ended to be removed from the session running
     */
    public void endGame(GameThread gameThread) {
        synchronized (sessions) {
            for (List<ClientHandler> ch : sessions.keySet()) {
                if (sessions.get(ch).equals(gameThread)) {
                    sessions.remove(ch);
                }
            }
        }
    }

    /**
     * Starts a new game between two client handlers and adds the
     * game to the sessions.
     */
    public void startGame() {
        synchronized (sessions) {
            if (getInQueue() >= 2) {
                ClientHandler p1 = playersQueue.remove(0);
                ClientHandler p2 = playersQueue.remove(0);
                List<ClientHandler> currentPlayers = new ArrayList<>();
                currentPlayers.add(p1);
                currentPlayers.add(p2);

                String name1 = p1.getUsername();
                String name2 = p2.getUsername();
                p1.recieveNewGame(Protocol.newGame(name1, name2));
                p2.recieveNewGame(Protocol.newGame(name1, name2));

                GameThread game = new GameThread(p1, p2, this);
                sessions.put(currentPlayers, game);
            }
        }
    }

    /**
     * Checks the number of players that are in the queue
     *
     * @return The size of the queue
     */
    public int getInQueue() {
        synchronized (playersQueue) {
            return playersQueue.size();
        }
    }

    /**
     * Query's the usernames of the players that are on the server
     *
     * @return A list of player's usernames
     */
    public List<String> getUsernames() {
        synchronized (players) {
            return new ArrayList<>(players.values());
        }
    }

    /**
     * Adds a new username to the list of the players stored in the server
     *
     * @param username      The name of the player to be added
     * @param clientHandler The client handler associated with the username
     */
    public void addUsername(String username, ClientHandler clientHandler) {
        synchronized (players) {
            players.put(clientHandler, username);
        }
    }

    /**
     * Checks if a client handler is in queue or not.
     *
     * @param clientHandler The client handler to be checked
     * @return True, if the client handler is in queue, otherwise, false
     */
    public boolean inQueue(ClientHandler clientHandler) {
        return playersQueue.contains(clientHandler);
    }

    /**
     * Adds a client handler to the queue.
     *
     * @param clientHandler The client handler to be added to the queue
     */
    public void queue(ClientHandler clientHandler) {
        synchronized (playersQueue) {
            playersQueue.add(clientHandler);
        }
    }

    /**
     * Remove a client handler from the queue.
     *
     * @param clientHandler The client handler to be removed from the queue
     */
    public void deQueue(ClientHandler clientHandler) {
        synchronized (playersQueue) {
            players.remove(clientHandler);
        }
    }

    /**
     * Plays a move received by the server from the client. If the move
     * is invalid, this client handier is closed
     *
     * @param index         The index of the move
     * @param clientHandler The client handler that sends the move
     */
    public void playMove(int index, ClientHandler clientHandler) {
        synchronized (sessions) {
            for (List<ClientHandler> ch : sessions.keySet()) {
                if (ch.contains(clientHandler)) {
                    GameThread currentGame = sessions.get(ch);
                    if (!currentGame.doMove(index)) {
                        clientHandler.close();
                    }
                }
            }
        }
    }
}









