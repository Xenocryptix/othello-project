package Othello.Server;

import Othello.exceptions.PortNumberException;

import java.util.Scanner;

public class ServerTUI {
    public static void main(String[] args) throws PortNumberException {
        Scanner input = new Scanner(System.in);

        System.out.print("Input a port number: ");
        int port = input.nextInt();

        Server server = new OthelloServer(port);
        server.start();

    }
}
