package NetworkingTest;

import org.junit.jupiter.api.Test;
import othello.controller.server.OthelloServer;
import othello.exceptions.PortNumberException;

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

}
