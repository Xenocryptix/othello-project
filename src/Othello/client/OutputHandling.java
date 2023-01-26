package Othello.client;

import java.io.*;
import java.net.*;

public class OutputHandling implements Runnable {

    Socket client;
    private final BufferedReader reader;
    public OutputHandling(Socket socket) throws IOException {
        this.client = socket;
        reader = new BufferedReader(new InputStreamReader(client.getInputStream()));
    }
    @Override
    public void run() {
        try {
            while (!client.isClosed()) {
                System.out.println(reader.readLine());
            }
        } catch (SocketException e) {
            System.out.println("Stopped");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
