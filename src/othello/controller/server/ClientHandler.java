package othello.controller.server;

import othello.controller.Protocol;

import java.io.*;
import java.net.Socket;

public class ClientHandler implements Runnable {
    private final Socket client;
    private final OthelloServer server;
    private final BufferedReader reader;
    private final PrintWriter writer;
    private String username;

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

    public void sendNewGame(String newGame) {
        writer.println(newGame);
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
                    case Protocol.HELLO:
                        writer.println(Protocol.handshake("Welcome"));
                        break;
                    case Protocol.LOGIN:
                        if (server.getUsernames().contains(splitted[1])) {
                            writer.println(Protocol.ALREADYLOGGEDIN);
                        } else {
                            username = splitted[1];
                            server.addUsername(splitted[1], this);
                            writer.println(Protocol.LOGIN);
                        }
                        break;
                    case Protocol.LIST:
                        writer.println(Protocol.list(server.getUsernames()));
                        break;
                    case Protocol.QUEUE:
                        if (server.inQueue(this)) {
                            server.deQueue(this);
                        } else {
                            server.queue(this);
                        }
                        break;
                    case Protocol.MOVE:
                        if (Integer.parseInt(splitted[1]) < 0 || Integer.parseInt(splitted[1]) > 64) {
                            close();
                        } else {
                            server.playMove(Integer.parseInt(splitted[1]), this);
                        }
                        break;
                    default:
                        writer.println(Protocol.ERROR);
                }
            }
            close(); //When a readline is null then the client has tried to quit, so the client handler must be closed
        } catch (IOException e) {
            close();
        }
    }
}
