package NetworkingTest;

import othello.controller.server.OthelloServer;
import othello.controller.server.Server;
import othello.exceptions.PortNumberException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ServerTest {
    private Server server;

    @BeforeEach
    public void setUp() {
        server = new OthelloServer(2222);
    }

    @Test
    public void testGames() throws PortNumberException {
        assertFalse(server.isAccepting());
        //start server
        server.start();
        assertTrue(server.isAccepting());
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);
    }
}
