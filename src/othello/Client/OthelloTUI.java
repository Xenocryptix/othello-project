package othello.Client;

import othello.exceptions.UnestablishedConnection;
import othello.model.Board;
import othello.players.HumanPlayer;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.PortUnreachableException;
import java.net.UnknownHostException;

public class OthelloTUI {
    public static void main(String[] args) throws IOException {
        String serverAddress;
        String username;
        String command;
        boolean connected;
        int port;
        BufferedReader input = new BufferedReader(new InputStreamReader(System.in));

        System.out.print("Enter a server address: ");
        serverAddress = input.readLine();

        System.out.print("Enter port number: ");
        port = Integer.parseInt(input.readLine());
        if (port < 0 || port > 65536) {
            throw new PortUnreachableException("Port number entered is invalid");
        }

        Listener clientListener = new ClientListener();
        OthelloClient client = new OthelloClient(clientListener);
        try {
            connected = client.connect(InetAddress.getByName(serverAddress), port);
            if (!connected) {
                throw new UnestablishedConnection("No connection was established");
            }
            client.sendHello("desc");
            System.out.print("Enter username: ");
            username = input.readLine();
            client.sendLogin(username);

            System.out.println("Enter a command: ");
            while (!(command = input.readLine()).equals("quit")) {
                switch (command.toLowerCase()) {
                    case "queue":
                        queue(input, client);
                        break;
                    case "list":
                        client.sendList();
                        break;
                    case "hint":
                        client.hint();
                        break;
                    default:
                        sendMove(command, client);
                }
                if (client.inGame()) {
                    System.out.println("Enter a move/command: ");
                }
            }
            client.close();

        } catch (UnknownHostException e) {
            System.out.println("You've entered an unknown host. Enter a valid one");
        } catch (UnestablishedConnection | PortUnreachableException e) {
            System.out.println(e.getMessage());
        } catch (IOException e) {
            System.out.println("You lost connection abruptly. Please fix your connection");
        }
    }

    private static void sendMove(String command, OthelloClient client) {
        if (client.inGame() && client.getPlayer() instanceof HumanPlayer) {
            if (command.equalsIgnoreCase("pass")) {
                client.sendMove(64);
            } else {
                int col = command.toUpperCase().charAt(0) - 65;
                int row = Integer.parseInt(String.valueOf(command.charAt(1))) - 1;
                int index = row * Board.DIM + col;
                if (!client.sendMove(index)) {
                    System.out.println("Please enter a valid move. If you want help enter: hint ");
                    client.sendMove(index);
                }
            }
        } else {
            System.out.println("Invalid command");
        }
    }

    private static void queue(BufferedReader input, OthelloClient client) throws IOException {
        if (!client.inGame()) {
            if (!client.isInQueue()) {
                System.out.println("Choose wisely: Human, Naive, Greedy");
                String character = input.readLine();
                while (!client.setPlayer(character)) {
                    System.out.println("Please enter a valid option: " +
                            "Human, Naive, Greedy");
                    character = input.readLine();
                }
                client.queue();
                System.out.println("Finding match, hold tight...");
            } else {
                client.queue();
                System.out.println("You've left the queue!");
            }
        }
    }
}

