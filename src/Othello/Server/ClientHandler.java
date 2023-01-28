package Othello.Server;

import java.io.*;
import java.net.Socket;

public class ClientHandler implements Runnable{
    private final Socket client;
    private final OthelloServer server;
    private final BufferedReader reader;
    private final PrintWriter writer;
    private String username;
    private String newGame;
    public static final Object QUEUED = new Object();

    public ClientHandler(Socket client, OthelloServer othelloServer) {
        this.client = client;
        try {
            reader = new BufferedReader(new InputStreamReader(client.getInputStream()));
            writer = new PrintWriter(new OutputStreamWriter(client.getOutputStream()), true);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        this.server = othelloServer;
    }

    public String getUsername() {
        return username;
    }
    public void recieveNewGame(String newGame) {
        this.newGame = newGame;
    }

    @Override
    public void run() {
        try {
            String command;
            while ((command = reader.readLine()) != null) {
                String[] splitted = command.split(Protocol.SEPARATOR);
                switch (splitted[0]) {
                    case "HELLO":
                        writer.println(Protocol.handshake("Welcome"));
                        break;
                    case "LOGIN":
                        if (server.getUsernames().contains(splitted[1])) {
                            writer.println(Protocol.ALREADYLOGGEDIN);
                        } else {
                            username = splitted[1];
                            server.addUsername(splitted[1], this);
                            writer.println(Protocol.LOGIN);
                        }
                        break;
                    case "LIST":
                        writer.println(Protocol.list(server.getUsernames()));
                        break;
                    case "QUEUE":
                        server.addToQueue(this);
                        server.startGame();
                        synchronized (this) {
                            try {
                                this.wait();
                                writer.println(newGame);
                            } catch (InterruptedException e) {
                                throw new RuntimeException(e);
                            }
                        }
                        break;
                    case "MOVE":

                }
            }
        } catch (IOException e) {
            e.getCause();
        }
    }
}
