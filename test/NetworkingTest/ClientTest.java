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
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ClientTest {
    private OthelloServer server;
    List<OthelloClient> clients;

    /**
     * Set up the server and initialize the list of clients
     * @throws PortNumberException
     * @throws UnknownHostException
     */
    @BeforeEach
    public void setUp() throws PortNumberException, UnknownHostException {
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
     * Test the communication between client and server
     * We check for each message sent, a correct reply is received
     * (Since no player object is assigned to clients, getting a NullPointerException is normal)
     * @throws InterruptedException
     * @throws UnknownHostException
     * @throws PortNumberException
     */
    @Test
    void testMessage() throws InterruptedException, UnknownHostException, PortNumberException {
        server.start();
        for (int i = 0; i < clients.size(); i++) {
            OthelloClient client = clients.get(i);
            //Test if each client is connected to the server
            assertTrue(client.connect(InetAddress.getByName("localhost"), 2222));
            client.sendHello();
            //Everytime we send a message, wait for 1 second for the client to receive
            TimeUnit.SECONDS.sleep(1);
            //Check if we receive a HELLO message
            assertTrue(client.getMessage().contains("HELLO"));

            //Check if the LOGIN message is received
            client.sendLogin("test_client" + i);
            TimeUnit.SECONDS.sleep(1);
            assertTrue(client.getMessage().contains("LOGIN"));

            //Check if the LIST message is correctly received
            client.sendList();
            TimeUnit.SECONDS.sleep(1);
            String list = client.getMessage();
            String[] splitted = list.split("~");
            assertTrue(list.contains("LIST"));
            assertEquals(i + 1, splitted.length - 1);

            //Join all of them in the queue, since there are 3 clients, the first two will
            //be matched and will receive a NEWGAME message
            client.queue();
            System.out.println("Joining queue");
            TimeUnit.SECONDS.sleep(1);
        }

        TimeUnit.SECONDS.sleep(1);
        //Check if the first two client receive a NEWGAME message
        String msg1 = clients.get(0).getMessage();
        String msg2 = clients.get(1).getMessage();
        String msg3 = clients.get(2).getMessage();
        System.out.println("\n\n\n" + msg1 + "\n" + msg2 + "\n" + msg3);
        System.out.println(server.getPlayers());
        String[] splitted = msg1.split("~");
        assertEquals(3, splitted.length);
        System.out.println(msg1);
        assertTrue(msg1.contains("NEWGAME"));
        System.out.println(msg2);
        assertTrue(msg2.contains("NEWGAME"));
        System.out.println(msg3);
        assertFalse(msg3.contains("NEWGAME"));

    }

}
