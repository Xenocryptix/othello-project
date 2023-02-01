package Othello.Server;

import Othello.exceptions.PortNumberException;

import java.util.Scanner;

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
