package NetworkingTest;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import othello.controller.server.OthelloServer;
import othello.exceptions.PortNumberException;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Test class to ensure that response from the server
 * is correct
 */

public class ServerResponses {
    private OthelloServer server;
    private Socket client1;
    private Socket client2;

    /**
     * Initialises the server as well as the two client that will
     * be used for testing purposes.
     *
     * @throws IOException Thrown when there's an error in getting local host
     * @throws PortNumberException Thrown when port number used to open the server is not open
     */
    @BeforeEach
    public void setUp() throws IOException, PortNumberException {
        server = new OthelloServer(0);
        server.start();
        client1 = new Socket(InetAddress.getLocalHost(), server.getPort());
        client2 = new Socket(InetAddress.getLocalHost(), server.getPort());
    }

    /**
     * Tests that the replies from the server are of correct protocol form
     */
    @Test
    public void testProtocolReplies() {
        String reply;
        // using a try-with-resources block, we ensure that reader/writer are closed afterwards
        try (BufferedReader reader2 = new BufferedReader(new InputStreamReader(client2.getInputStream()));
             PrintWriter writer2 = new PrintWriter(new OutputStreamWriter(client2.getOutputStream()), true);
             BufferedReader reader1 = new BufferedReader(new InputStreamReader(client1.getInputStream()));
             PrintWriter writer1 = new PrintWriter(new OutputStreamWriter(client1.getOutputStream()), true)) {

            //Ensures that when HELLO is sent, a response is sent back from the server
            writer1.println("HELLO");
            reply = reader1.readLine();
            assertEquals("HELLO~Welcome to the server!", reply);
            writer2.println("HELLO");
            reply = reader2.readLine();
            assertEquals("HELLO~Welcome to the server!", reply);


            //Ensures that logging in is correct and duplicate usernames are detected
            writer1.println("LOGIN~Moamen");
            reply = reader1.readLine();
            assertEquals("LOGIN", reply);


            //Ensures that logging in with a used username is rejected
            writer2.println("LOGIN~Moamen");
            reply = reader2.readLine();
            assertEquals("ALREADYLOGGEDIN", reply);
            writer2.println("LOGIN~Mo");
            reply = reader2.readLine();
            assertEquals("LOGIN", reply);

            //Ensures that when a move is sent in the wrong
            // format, it sends back an error
            writer1.println("move~64");
            reply = reader1.readLine();
            assertEquals("ERROR", reply);

            //Here contains is used as message can have different order when it is called each time
            writer1.println("LIST");
            reply = reader1.readLine();
            assertTrue(reply.contains("Mo") && reply.contains("Moamen") && reply.contains("LIST"));

            //Sleep is used to wait for fields to be updated
            assertEquals(0, server.getInQueue());
            writer1.println("QUEUE");
            Thread.sleep(1);
            assertEquals(1, server.getInQueue());

            writer1.println("QUEUE");
            Thread.sleep(1);
            assertEquals(0, server.getInQueue());

            writer1.println("QUEUE");
            writer2.println("QUEUE");

            //Ensures that NEWGAME message is correct
            reply = reader1.readLine();
            assertEquals("NEWGAME~Moamen~Mo", reply);
            reply = reader2.readLine();
            assertEquals("NEWGAME~Moamen~Mo", reply);

            client1.close();
            client2.close();
        } catch (IOException | InterruptedException e) {
            System.out.println("Error in reading/writing");
        }
    }
}
