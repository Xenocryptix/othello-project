package NetworkingTest;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import othello.controller.client.OthelloClient;
import othello.controller.server.ClientHandler;
import othello.controller.server.OthelloServer;
import othello.exceptions.ConnectionDropped;
import othello.exceptions.PortNumberException;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

import static org.junit.jupiter.api.Assertions.assertThrows;


public class ExceptionTest {
    /**
     * Tests that not two servers can connect to the same
     * port number
     *
     * @throws PortNumberException Thrown when trying to connect to a taken port
     */
    @Test
    public void testPortNumberException() throws PortNumberException {
        OthelloServer initialServer = new OthelloServer(2222);
        initialServer.start();
        OthelloServer testServer = new OthelloServer(2222);
        assertThrows(PortNumberException.class, () -> testServer.start(), "The specified port is invalid or unavailable");
    }

    @Test
    public void testConnectionDroppedExcetion() throws ConnectionDropped, IOException, PortNumberException {
        OthelloServer server = new OthelloServer(0);
        server.start();
        Socket client1 = new Socket(InetAddress.getLocalHost(),server.getPort());
        ClientHandler clientHandler1 = new ClientHandler(client1,server);
        Socket client2 = new Socket(InetAddress.getLocalHost(),server.getPort());
        ClientHandler clientHandler2 = new ClientHandler(client2,server);

        try (BufferedReader reader2 = new BufferedReader(new InputStreamReader(client2.getInputStream()));
             PrintWriter writer2 = new PrintWriter(new OutputStreamWriter(client2.getOutputStream()), true);
             BufferedReader reader1 = new BufferedReader(new InputStreamReader(client1.getInputStream()));
             PrintWriter writer1 = new PrintWriter(new OutputStreamWriter(client1.getOutputStream()), true)) {
            writer1.println("HELLO");
            writer2.println("HELLO");
            writer1.println("LOGIN~MO");
            writer2.println("LOGIN~WO");

            writer1.println("QUEUE");
            writer2.println("QUEUE");


            assertThrows(ConnectionDropped.class, () -> server.removeClient(clientHandler1));
        }

    }
}
