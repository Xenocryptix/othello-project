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
    private static String serverAddress;
    private static int port;
    private static final String GREEN = "\033[0;32m";
    public static final String RESET = "\033[0m";

    public static void main(String[] args) {
        OthelloTUI tui = new OthelloTUI();
        try {
            tui.run();
        } catch (IOException e) {
            System.out.println(e.getMessage());
            ;
        }
    }


    public void run() throws IOException {

        BufferedReader input = new BufferedReader(new InputStreamReader(System.in));

        initiate(input);

        Listener clientListener = new ClientListener();
        OthelloClient client = new OthelloClient(clientListener);
        try {
            boolean connected = client.connect(InetAddress.getByName(serverAddress), port);
            if (!connected) {
                throw new UnestablishedConnection("No connection was established");
            }
            client.sendHello("desc");

            login(input, client);

            help();

            System.out.println("Enter a command: ");
            String command;
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
                    case "help":
                        help();
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

    private static void initiate(BufferedReader input) throws IOException {
        System.out.print("Enter a server address: ");
        serverAddress = input.readLine();

        System.out.print("Enter port number: ");
        port = Integer.parseInt(input.readLine());
        if (port < 0 || port > 65536) {
            throw new PortUnreachableException("Port number entered is invalid");
        }
    }

    private static void login(BufferedReader input, OthelloClient client) throws IOException {
        System.out.print("Enter username: ");
        String username = input.readLine();
        client.sendLogin(username); //TODO: ALREADYLOGGEDIN
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
                System.out.println("Choose wisely: Human (H), Naive (N), Greedy (G)");
                String character = input.readLine();
                while (!client.setPlayer(character)) {
                    System.out.println("Please enter a valid option: " +
                            "Human (H), Naive (N), Greedy (N)");
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

    private static void help() {
        System.out.print(
                GREEN + "Commands:\n" +
                GREEN + "queue" + " ................. join/leave the queue \n" +
                GREEN + "list" + "  ................. get a list of all players\n" +
                GREEN + "hint" + "  ................. a move that can be played\n" +
                GREEN + "help" + " .................. help (this menu)\n" + RESET );
    }
}


