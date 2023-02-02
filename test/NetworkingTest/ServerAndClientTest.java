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
 * Responsible for testing the server and client together
 */
public class ServerAndClientTest {
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
        for (int i = 0; i < 10; i++) {
            ClientListener clientListener = new ClientListener();
            OthelloClient client = new OthelloClient();
            client.addListener(clientListener);
            clients.add(client);
        }
    }

    /**
     * Test the basic functionalities of server, being able to retrieve the player list
     * and matching the players in the queue, and allowing players to play a game
     *
     * @throws PortNumberException  Thrown if port is not defined
     * @throws UnknownHostException Thrown if the server address is not found
     * @throws InterruptedException Thrown if there was a problem with sleeping
     */
    @Test
    public void testPlayingASingleGame() throws UnknownHostException, PortNumberException, InterruptedException {
        assertFalse(server.isAccepting());
        //Start the server, and check if the server is accepting and have a valid port
        server.start();
        assertTrue(server.isAccepting());
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);


        //Connecting the first client to the server and adding him to the queue
        clients.get(0).connect(InetAddress.getByName("localhost"), server.getPort());
        clients.get(0).sendHello();
        clients.get(0).sendLogin("player 1");
        clients.get(0).setPlayer("g");
        clients.get(0).queue();

        //Adding sleep to wait for the lists to get updated
        TimeUnit.SECONDS.sleep(1);
        assertTrue(server.getUsernames().contains("player 1"));
        assertEquals(1, server.getInQueue());

        //Connecting the second client to the server and adding him to the queue
        clients.get(1).connect(InetAddress.getByName("localhost"), server.getPort());
        clients.get(1).sendHello();
        clients.get(1).sendLogin("player 2");
        clients.get(1).setPlayer("n");
        clients.get(1).queue();

        //Adding sleep to wait for the lists to get updated
        TimeUnit.SECONDS.sleep(1);
        assertTrue(server.getUsernames().contains("player 2"));

        //This ensures that the two players are not in the queue anymore and are in a game
        assertEquals(0, server.getInQueue());

    }

    /**
     * Tests the servers when 4 clients queue
     * and how the server reacts to them queuing
     *
     * @throws PortNumberException  Thrown if port number is taken
     * @throws UnknownHostException Thrown if host is unknown
     * @throws InterruptedException Thrown if an error happens during sleeping
     */
    @Test
    public void testPlayingTwo() throws PortNumberException, UnknownHostException, InterruptedException {
        assertFalse(server.isAccepting());
        //Start the server, and check if the server is accepting and have a valid port
        server.start();
        assertTrue(server.isAccepting());
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);

        for (int i = 0; i < 4; i++) {
            clients.get(i).setPlayer("g");
            clients.get(i).connect(InetAddress.getByName("localhost"), server.getPort());
            clients.get(i).sendHello();
            clients.get(i).sendLogin("player " + i);
        }

        clients.get(0).queue();
        TimeUnit.SECONDS.sleep(1);
        clients.get(1).queue();
        TimeUnit.SECONDS.sleep(1);
        clients.get(2).queue();
        TimeUnit.SECONDS.sleep(1);
        clients.get(3).queue();
        TimeUnit.SECONDS.sleep(1);
    }

    /**
     * Tests when 10 clients join the server and queue
     *
     * @throws PortNumberException  Thrown if port is not defined
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
            clients.get(i).setPlayer("g");
            client.connect(InetAddress.getByName("localhost"), server.getPort());
            client.sendHello();
            client.sendLogin("test_client " + i);
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
