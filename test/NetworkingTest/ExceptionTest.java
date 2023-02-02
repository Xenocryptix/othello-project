package NetworkingTest;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import othello.controller.client.OthelloClient;
import othello.controller.server.OthelloServer;
import othello.exceptions.ConnectionDropped;
import othello.exceptions.PortNumberException;

import java.net.InetAddress;
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
    public void testConnectionDroppedExcetion() throws ConnectionDropped, UnknownHostException {
        OthelloClient client1 = new OthelloClient();
        OthelloClient client2 = new OthelloClient();
        client1.connect(InetAddress.getLocalHost(), 2222);
        client2.connect(InetAddress.getLocalHost(), 2222);
        client1.sendHello();
        client2.sendHello();
        client1.sendLogin("mo");
        client2.sendLogin("wo");

        client1.setPlayer("h");
        client2.setPlayer("h");

        client1.queue();
        client2.queue();

        assertThrows(ConnectionDropped.class, () -> client1.close(),"mo lost connection during the game" );
    }
}
