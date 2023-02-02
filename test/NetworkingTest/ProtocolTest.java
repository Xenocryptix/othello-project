package NetworkingTest;

import org.junit.jupiter.api.Test;
import othello.controller.Protocol;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests that the protocol class correctly creates the protocol messages.
 */
public class ProtocolTest {
    /**
     * Tests that the generation of the protocol messages
     * from the test class are correct.
     */
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
        assertEquals("GAMEOVER~DISCONNECT~Bob", Protocol.gameover(new String[]{"disconnect", "Bob"}));
        assertEquals("GAMEOVER~DRAW", Protocol.gameover(new String[]{"draw"}));
        assertEquals("GAMEOVER~VICTORY~Bob", Protocol.gameover(new String[]{"victory", "Bob"}));
    }
}
