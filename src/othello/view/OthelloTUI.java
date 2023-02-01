package othello.view;


import othello.controller.client.ClientListener;
import othello.controller.client.Listener;
import othello.controller.client.OthelloClient;
import othello.model.Board;
import othello.model.players.HumanPlayer;
import othello.model.players.ai.ComputerPlayer;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.PortUnreachableException;
import java.net.UnknownHostException;

public class OthelloTUI {
    private static String serverAddress;
    private static int port = -1;
    private static final String GREEN = "\033[0;32m";
    private static final String RESET = "\033[0m";
    private static final SoundEffect error = new SoundEffect("src/othello/view/error.wav");
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


        Listener clientListener = new ClientListener();
        OthelloClient client = new OthelloClient();
        client.addListener(clientListener);

        try {
            boolean connected = false;
            while (!connected) {
                initiate(input);
                if (port >= 0 && port <= 65536) {
                    connected = client.connect(InetAddress.getByName(serverAddress), port);
                    if (!connected) {
                        System.out.println("Can not connect to the specified server");
                        error.play();
                    }
                } else {
                    System.out.println("Invalid port");
                    error.play();
                }
            }

            synchronized (OthelloClient.CONNECTLOCK) {
                OthelloClient.CONNECTLOCK.wait();
                login(input, client);
            }

            help();

            String command;
            while ((command = input.readLine()) != null) {
                if (command.equals("quit")) {
                    if (!client.inGame()) {
                        break;
                    } else {
                        System.out.println("You can't leave while in game!");
                    }
                }
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
                    System.out.print("Enter a move or command: ");
                }
            }
            client.close();

        } catch (UnknownHostException e) {
            System.out.println("Host unknown. There may be a typo in your address, or the server is closed");
        } catch (PortUnreachableException e) {
            System.out.println(e.getMessage());
        } catch (IOException e) {
            System.out.println("You lost connection abruptly. Please fix your connection");
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    private static void initiate(BufferedReader input) throws IOException {
        System.out.print("Enter a server address: ");
        serverAddress = input.readLine();

        System.out.print("Enter port number: ");
        String portStr = input.readLine();
        if (portStr.length() > 0 && portStr.length() < 6) {
            port = Integer.parseInt(portStr);
        }
    }

    private static void login(BufferedReader input, OthelloClient client) throws IOException {
        synchronized (OthelloClient.LOGINLOCK) {
            try {
                while (!client.isLoggedIn()) {
                    System.out.print("Enter username: ");
                    String username = input.readLine();
                    if (!client.sendLogin(username)) {
                        continue;
                    }
                    OthelloClient.LOGINLOCK.wait();
                }
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
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
                        GREEN + "help" + " .................. help (this menu)\n" + RESET);
    }
}
