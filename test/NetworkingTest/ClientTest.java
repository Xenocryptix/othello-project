package NetworkingTest;

import othello.controller.client.ClientListener;
import othello.controller.client.Listener;
import othello.controller.client.OthelloClient;
import othello.controller.server.OthelloServer;
import othello.exceptions.PortNumberException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ClientTest {
    private OthelloServer server;
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
        client = new OthelloClient();
        client.addListener(clientListener);

    }

    @Test
    void testMessage() throws InterruptedException, UnknownHostException {
        assertTrue(client.connect(InetAddress.getByName("localhost"), 2222));

        client.sendHello();
        TimeUnit.SECONDS.sleep(1);
        assertTrue(client.getMessage().contains("HELLO"));

        client.sendLogin("test_client");
        TimeUnit.SECONDS.sleep(1);
        assertTrue(client.getMessage().contains("LOGIN"));

        client.sendList();
        TimeUnit.SECONDS.sleep(1);
        assertTrue(client.getMessage().contains("LIST"));

        client.queue();
        TimeUnit.SECONDS.sleep(1);
        assertEquals(1, server.getInQueue());
        client.queue();
        TimeUnit.SECONDS.sleep(1);
        assertEquals(0, server.getInQueue());
    }

}
