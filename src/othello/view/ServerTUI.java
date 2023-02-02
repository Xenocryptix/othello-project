package othello.view;

import othello.controller.server.OthelloServer;
import othello.exceptions.PortNumberException;

import java.util.Scanner;

/**
 * TUI which is responsible for creating the server at a certain port.
 */
public class ServerTUI {

    public static void main(String[] args) throws PortNumberException {
        Scanner input = new Scanner(System.in);

        OthelloServer server;
        boolean started = false;
        while (!started) {
            System.out.print("Input a valid port number: ");
            int port = input.nextInt();
            server = new OthelloServer(port);
            server.start();
            started = server.isStarted();
        }
        System.out.println("Server successfully started!");
    }
}
