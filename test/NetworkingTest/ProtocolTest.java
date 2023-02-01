package NetworkingTest;

import othello.controller.server.OthelloServer;
import othello.controller.Protocol;
import othello.controller.server.Server;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

public class ProtocolTest {
    @BeforeEach
    public void setUp() {
        Server server = new OthelloServer(2222);
    }
    @Test
    public void generationOfProtocol() {
        //Ensures that the hello protocol message is generated correctly
        assertEquals("HELLO~Client By Moamen", Protocol.handshake("Client By Moamen"));

        //Ensures that the login protocol message is generated correctly
        assertEquals("LOGIN~Moamen", Protocol.login("Moamen"));

        //Ensures that the list protocol message is generated correctly
        assertEquals("LIST~Tom~Max~Alex", Protocol.list(List.of(new String[]{"Tom", "Max", "Alex"})));
        assertEquals("LIST~Tom", Protocol.list(List.of(new String[]{"Tom"})));

        //Ensures that the newgame protocol message is generated correctly
        assertEquals("NEWGAME~Tom~Max", Protocol.newGame("Tom", "Max"));

        //Ensures that the move protocol message is generated correctly
        assertEquals("MOVE~22", Protocol.move(22));

        //Ensures that the game over protocol message is generated correctly
        assertEquals("GAMEOVER~DISCONNECT~Bob", Protocol.gameover(new String[]{"disconnect","Bob"}));
        assertEquals("GAMEOVER~DRAW", Protocol.gameover(new String[]{"draw"}));
        assertEquals("GAMEOVER~VICTORY~Bob", Protocol.gameover(new String[]{"victory", "Bob"}));
    }
}
