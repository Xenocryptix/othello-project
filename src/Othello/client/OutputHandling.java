package Othello.client;

import java.io.*;
import java.net.*;

public class OutputHandling implements Runnable {

    OthelloClient client;
    private final BufferedReader reader;
    public OutputHandling(OthelloClient client) throws IOException {
        this.client = client;
        var pw1 = client.getPipedWriter();
        PipedReader pr = new PipedReader(pw1);
        reader = new BufferedReader(pr);
    }
    @Override
    public void run() {
        try {
            while (!client.closed()) {
                System.out.println(reader.readLine());
            }
        } catch (SocketException e) {
            System.out.println("Stopped");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
