package NetworkingTest;

import Othello.Server.OthelloServer;
import Othello.Server.Server;
import org.junit.jupiter.api.BeforeEach;

public class ProtocolTest {
    @BeforeEach
    public void setUp() {
        Server server = new OthelloServer(2222);
    }
}
