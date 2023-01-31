package Othello.Server;

import java.util.Scanner;

public class ServerTUI {
    public static void main(String[] args) {
        Scanner input = new Scanner(System.in);

        System.out.print("Input a port number: ");
        int port = input.nextInt();

        while (port < 0 || port > 65535) {
            System.out.println("Please enter a valid port number");
            port = input.nextInt();
        }
        Server server = new OthelloServer(port);
        server.start();

    }
}
