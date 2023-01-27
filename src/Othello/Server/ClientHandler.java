package Othello.Server;

import java.io.*;
import java.net.Socket;

public class ClientHandler implements Runnable{
    private final Socket client;
    private final OthelloServer server;
    private final BufferedReader reader;
    private final PrintWriter writer;

    public ClientHandler(Socket client, OthelloServer othelloServer) {
        this.client = client;
        try {
            reader = new BufferedReader(new InputStreamReader(client.getInputStream()));
            writer = new PrintWriter(new OutputStreamWriter(client.getOutputStream()));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        this.server = othelloServer;
    }

    @Override
    public void run() {

    }
}
