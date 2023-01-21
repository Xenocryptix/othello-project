package Othello.client;

import Othello.Server.OthelloServer;
import Othello.Server.Protocol;
import Othello.Server.Server;

import java.io.*;
import java.net.Socket;

public class ClientHandler implements Runnable {
    private final Server othelloServer;
    private final Socket socket;
    private final BufferedReader reader;
    private final BufferedWriter writer;

    public ClientHandler(Socket socket, OthelloServer othelloServer) {
        this.othelloServer = othelloServer;
        this.socket = socket;
        try {
            reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void run() {

    }
}
