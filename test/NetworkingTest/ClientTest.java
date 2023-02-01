package NetworkingTest;

import Othello.Client.ClientListener;
import Othello.Client.Listener;
import Othello.Client.OthelloClient;
import Othello.Server.OthelloServer;
import Othello.Server.Server;
import Othello.exceptions.PortNumberException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;

import static Othello.Client.OthelloClient.CONNECTLOCK;
import static Othello.Client.OthelloClient.LOGINLOCK;
import static org.junit.Assert.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ClientTest {
    private Server server;
    Listener clientListener;
    OthelloClient client;

    /**
     * Set up the server and initialize the client components
     * @throws PortNumberException
     * @throws UnknownHostException
     */
    @BeforeEach
    public void setUp() throws PortNumberException, UnknownHostException {
        server = new OthelloServer(2222);
        server.start();
        clientListener = new ClientListener();
        client = new OthelloClient(clientListener);
        client.connect(InetAddress.getByName("localhost"), 2222);
    }

    @Test
    public void testMessage() throws InterruptedException {
        client.sendHello("Test class");
        synchronized (CONNECTLOCK) {
            System.out.println("Waiting...");
            CONNECTLOCK.wait();
            assertTrue(client.getMessage().contains("HELLO"));
        }

        client.sendLogin("test_client");
        synchronized (LOGINLOCK) {
            LOGINLOCK.wait();
            assertTrue(client.getMessage().contains("LOGIN"));
        }

        client.sendList();

    }

}
