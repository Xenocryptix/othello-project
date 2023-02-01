package othello.controller.server;


import othello.controller.Protocol;
import othello.exceptions.ConnectionDropped;
import othello.exceptions.PortNumberException;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;

//TODO
public class OthelloServer implements Server, Runnable {
    private final Map<ClientHandler, String> players;
    private final Map<List<ClientHandler>, PlayingGame> sessions;
    private final Queue<ClientHandler> playersQueue;
    private final int port;
    private final Thread serverThread;
    private ServerSocket serverSocket;
    private boolean started = false;

    //TODO
    public OthelloServer(int port) {
        this.port = port;
        playersQueue = new ArrayDeque<>();
        serverThread = new Thread(this);
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
    public void start() throws PortNumberException {
        try {
            serverSocket = new ServerSocket(port);
            serverThread.start();
            started = true;
        } catch (IOException e) {
            started = false;
            throw new PortNumberException();
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

    public boolean isStarted() {
        return started;
    }

    /**
     * Query on the players that are in the queue
     *
     * @return The list of client handlers that are in queue
     */
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
     * Ends a session of a game when the game is over from the PlayingGame
     * class.
     *
     * @param playingGame The game that is ended to be removed from the session running
     */
    public void endGame(PlayingGame playingGame) {
        synchronized (sessions) {
            for (List<ClientHandler> ch : sessions.keySet()) {
                if (sessions.get(ch).equals(playingGame)) {
                    sessions.remove(ch);
                    break;
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
                ClientHandler p1 = playersQueue.remove();
                ClientHandler p2 = playersQueue.remove();
                List<ClientHandler> currentPlayers = new ArrayList<>();
                currentPlayers.add(p1);
                currentPlayers.add(p2);

                String name1 = p1.getUsername();
                String name2 = p2.getUsername();
                p1.sendNewGame(Protocol.newGame(name1, name2));
                p2.sendNewGame(Protocol.newGame(name1, name2));

                PlayingGame game = new PlayingGame(p1, p2, this);
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
        synchronized (playersQueue) {
            return playersQueue.contains(clientHandler);
        }
    }

    /**
     * Adds a client handler to the queue.
     *
     * @param clientHandler The client handler to be added to the queue
     */
    public void queue(ClientHandler clientHandler) {
        synchronized (playersQueue) {
            playersQueue.add(clientHandler);
            if (getInQueue() >= 2) {
                startGame();
            }
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
        PlayingGame game = getGame(clientHandler);
        if (!game.doMove(index)) {
            clientHandler.close();
        }
    }
    /**
     * When a client abruptly disconnects, this method is called
     * to remove this player from the server as well as ensure that
     * the player is removed from the queue.
     *
     * @param clientHandler The client handler that disconnected
     * @throws ConnectionDropped
     */
    public void removeClient(ClientHandler clientHandler) throws ConnectionDropped {
        synchronized (players) {
            players.remove(clientHandler);
            playersQueue.remove(clientHandler);
            if (inGame(clientHandler)) {
                throw new ConnectionDropped("Player was in game");
            }
        }
    }

    /**
     * Checks if a certain client handler is in a game or not.
     *
     * @param clientHandler The client handler to be checked
     * @return True, if the player is in a game and false otherwise
     */
    public boolean inGame(ClientHandler clientHandler) {
        synchronized (sessions) {
            PlayingGame game = getGame(clientHandler);
            return game != null;
        }
    }

    /**
     * Gets the game of the client handler passed by going through
     * the current running sessions.
     *
     * @param clientHandler The client to be checked
     * @return the game if he is in one, or null if he is not
     */
    public PlayingGame getGame(ClientHandler clientHandler) {
        synchronized (sessions) {
            for (List<ClientHandler> ch : sessions.keySet()) {
                if (ch.contains(clientHandler)) {
                    return sessions.get(ch);
                }
            }
        }
        return null;
    }
}









