package NetworkingTest;

import othello.controller.client.ClientListener;
import othello.controller.client.Listener;
import othello.controller.client.OthelloClient;
import othello.controller.server.OthelloServer;
import othello.controller.server.Server;
import othello.exceptions.PortNumberException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.params.shadow.com.univocity.parsers.common.ArgumentUtils.indexOf;

public class ServerTest {
    private OthelloServer server;
    List<OthelloClient> clients;

    /**
     * Set up the server and initialize the list of clients
     * @throws PortNumberException
     * @throws UnknownHostException
     */
    @BeforeEach
    public void setUp() throws PortNumberException {
        //Initializing the server object
        server = new OthelloServer(2222);
        //Initializing clients
        clients = new ArrayList<>();
        for (int i = 0; i < 3; i++) {
            ClientListener clientListener = new ClientListener();
            OthelloClient client = new OthelloClient();
            client.addListener(clientListener);
            clients.add(client);
        }
    }

    /**
     * Test the basic functionalities of server, being able to retrieve the player list
     * and matching the players in the queue
     * (Since no player object is assigned to clients, getting a NullPointerException is normal)
     * @throws PortNumberException
     * @throws UnknownHostException
     * @throws InterruptedException
     */
    @Test
    public void testGames() throws PortNumberException, UnknownHostException, InterruptedException {
        assertFalse(server.isAccepting());
        //Start the server, and check if the server is accepting and have a valid port
        server.start();
        assertTrue(server.isAccepting());
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);

        for (int i = 0; i < clients.size(); i++) {
            OthelloClient client = clients.get(i);
            client.connect(InetAddress.getByName("localhost"), 2222);
            client.sendHello();
            client.sendLogin("test_client" + i);
            client.sendList();
            TimeUnit.SECONDS.sleep(1);
            assertEquals((i + 1), server.getPlayers().size());
            //Check if the player list is queried correctly

            //At any time, the queue size must not be greater than 2
            client.queue();
            TimeUnit.SECONDS.sleep(1);
            System.out.println(server.getQueue());
            assertEquals((i + 1) % 2, server.getInQueue());
        }
    }
}
