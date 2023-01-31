package Othello.Client;

import Othello.exceptions.*;
import Othello.model.Board;
import Othello.model.players.HumanPlayer;
import Othello.model.players.ai.ComputerPlayer;

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
                throw new UnestablishedConnection();
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
                        if (client.inGame()) {
                            sendMove(command, client);
                        } else {
                            System.out.println("Unknown command.\nFor available commands, type HELP");
                        }
                }
                if (client.inGame() && client.checkTurn()) {
                    System.out.println("Enter a move/command: ");
                }
            }
            client.close();

        } catch (UnknownHostException e) {
            System.out.println("Host unknown. There may be a typo in your address, or the server is closed");
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
            throw new PortUnreachableException("The specified port is invalid or unavailable");
        }
    }

    private static void login(BufferedReader input, OthelloClient client) throws IOException {
        System.out.print("Enter username: ");
        String username = input.readLine();
        client.sendLogin(username);
    }

    private static void sendMove(String command, OthelloClient client) {
        if (client.getPlayer() instanceof HumanPlayer) {
            if (command.equalsIgnoreCase("pass")) {
                client.sendMove(64);
            } else if (Character.isAlphabetic(command.charAt(0)) && Character.isDigit(command.charAt(1))) {
                int col = command.toUpperCase().charAt(0) - 65;
                int row = Integer.parseInt(String.valueOf(command.charAt(1))) - 1;
                int index = row * Board.DIM + col;
                if (!client.checkTurn()) {
                    System.out.println("It's not your turn yet. Please wait");
                } else if (!client.sendMove(index)) {
                    System.out.println("This is not a legal move. Please enter a valid move\n" +
                            "You can type HINT if you're unsure of where to move");
                } else {
                    client.sendMove(index);
                }
            } else {
                System.out.println("Unknown command or invalid move format.\n" +
                        "Your move should be in the format of a letter followed by a number, e.g. \"C5\" \n" +
                        "For available commands, type HELP");
            }
        } else if (client.getPlayer() instanceof ComputerPlayer) {
            System.out.println("You can not move while playing as a bot!");
        }
    }

    private static void queue(BufferedReader input, OthelloClient client) throws IOException {
        if (!client.inGame()) {
            if (!client.isInQueue()) {
                System.out.println("Choose wisely: Human (H), Naive (N), Greedy (G)");
                String character = input.readLine();
                while (!client.setPlayer(character)) {
                    System.out.println("Please enter a valid option: " +
                            "Human (H), Naive (N), Greedy (G)");
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


