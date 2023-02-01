package NetworkingTest;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import othello.controller.client.ClientListener;
import othello.controller.client.OthelloClient;
import othello.controller.server.OthelloServer;
import othello.exceptions.PortNumberException;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Responsible for testing the server side
 */
public class ServerTest {
    List<OthelloClient> clients;
    private OthelloServer server;

    /**
     * Set up the server and initialize the list of clients
     */
    @BeforeEach
    public void setUp() {
        //Initializing the server object
        server = new OthelloServer(0);
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
     *
     * @throws PortNumberException Thrown if port is not defined
     * @throws UnknownHostException Thrown if the server address is not found
     * @throws InterruptedException Thrown if there was a problem with sleeping
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
            client.connect(InetAddress.getByName("localhost"), server.getPort());
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
