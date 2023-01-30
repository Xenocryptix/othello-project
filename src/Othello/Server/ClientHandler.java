package Othello.Server;

import java.io.*;
import java.net.Socket;

import static Othello.Server.Protocol.*;

public class ClientHandler implements Runnable {
    private final Socket client;
    private final OthelloServer server;
    private final BufferedReader reader;
    private final PrintWriter writer;
    public static final Object LOCK = new Object();
    private String username;
    private String newGame;

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

    public void close() {
        try {
            server.removeClient(this);
            client.close();
            writer.close();
            reader.close();
        } catch (IOException e) {
            System.out.println("Close error");
        }
    }

    public void setMove(int index) {
        server.playMove(index, this);
    }

    public void sendMove(int index) {
        writer.println(Protocol.move(index));
    }

    public void sendMessage(String message) {
        writer.println(message);
    }


    @Override
    public void run() {
        try {
            String command;
            while ((command = reader.readLine()) != null) {
                String[] splitted = command.split(Protocol.SEPARATOR);
                switch (splitted[0]) {
                    case HELLO:
                        writer.println(Protocol.handshake("Welcome"));
                        break;
                    case LOGIN:
                        if (server.getUsernames().contains(splitted[1])) {
                            writer.println(Protocol.ALREADYLOGGEDIN);
                        } else {
                            username = splitted[1];
                            server.addUsername(splitted[1], this);
                            writer.println(Protocol.LOGIN);
                        }
                        break;
                    case LIST:
                        writer.println(Protocol.list(server.getUsernames()));
                        break;
                    case QUEUE:
                        server.addToQueue(this);
                        synchronized (LOCK) {
                            try {
                                while (server.getInQueue() < 2) {
                                    LOCK.wait();
                                }
                                server.startGame();
                                writer.println(newGame);
                            } catch (InterruptedException e) {
                                throw new RuntimeException(e);
                            }
                        }
                        break;
                    case MOVE:
                        if (Integer.parseInt(splitted[1]) < 0 ||
                                Integer.parseInt(splitted[1]) > 64) {
                            close();
                        }
                        setMove(Integer.parseInt(splitted[1]));
                }
            }
        } catch (IOException e) {
            e.getCause();
        }
    }
}
