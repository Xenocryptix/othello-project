package NetworkingTest;

import Othello.Client.ClientListener;
import Othello.Client.Listener;
import Othello.Client.OthelloClient;
import Othello.Server.OthelloServer;
import Othello.Server.Server;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.net.InetAddress;
import java.net.UnknownHostException;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ServerAndClientTest {
    private Server server;

    @BeforeEach
    public void setUp() {
        server = new OthelloServer(2222);
    }

    @Test
    public void testGames() throws UnknownHostException {
        assertFalse(server.isAccepting());

        //start server
        server.start();

        assertTrue(server.isAccepting());
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);

        Listener listener = new ClientListener();
//        OthelloClient client = new OthelloClient();
//        client.connect(InetAddress.getLocalHost(), server.getPort());


    }
}
