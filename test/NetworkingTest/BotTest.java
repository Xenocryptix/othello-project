package NetworkingTest;

import Othello.Server.OthelloServer;
import Othello.Server.Server;
import Othello.exceptions.PortNumberException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class BotTest {
    private Server server;
    private List<BotClient> bots = new ArrayList<>();
    private List<Thread> threads = new ArrayList<>();

    @BeforeEach
    public void setUp() {
        server = new OthelloServer(2222);
        for (int i = 0; i < 2; i++) {
            bots.add(new BotClient(i));
        }
    }

    @Test
    public void testGames() throws PortNumberException {
        assertFalse(server.isAccepting());

        //start server
        server.start();

        assertTrue(server.isAccepting());
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);
        for (BotClient i: bots) {
            Thread t = new Thread(i);
            threads.add(t);
            t.start();
        }
        try {
            for (Thread t: threads) {
                t.join();
            }
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        for (BotClient bot: bots) {
            assertTrue(bot.isPassed());
        }
    }
}
