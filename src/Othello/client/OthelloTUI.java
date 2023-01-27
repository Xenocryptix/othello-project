package Othello.client;

import Othello.model.Board;
import Othello.players.HumanPlayer;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.SocketException;
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
            throw new NumberFormatException();
        }
        Listener clientListener = new ClientListener();
        OthelloClient client = new OthelloClient(clientListener);
        try {
            connected = client.connect(InetAddress.getByName(serverAddress), port);
            if (!connected) {
                throw new SocketException();
            }
            client.sendHello("desc");
            System.out.print("Enter username: ");
            username = input.readLine();
            client.sendLogin(username);


            while (!(command = input.readLine()).equals("quit")) {
                if (client.getStatus()) {
                    System.out.println("Enter a move/command: ");
                } else {
                    System.out.println("Enter a command: ");
                }
                switch (command.toLowerCase()) {
                    case "queue":
                        if (!client.getStatus()) {
                            System.out.println("Choose wisely: Human, Naive, Greedy");
                            String character = input.readLine();
                            client.setPlayer(character);
                            client.queue();
                        } else {
                            System.out.println("You can't use this command in game!");
                        }
                        break;
                    case "list":
                        client.sendList();
                        break;
                    default:
                        if (client.getStatus() && client.getPlayer() instanceof HumanPlayer) {
                            if (command.equals("PASS")) {
                                client.sendMove(64);
                            } else {
                                int col = (command).toUpperCase().charAt(0) - 65;
                                int row = Integer.parseInt(String.valueOf(command.charAt(1))) - 1;
                                int index = row * Board.DIM + col;
                                if (!client.sendMove(index)) {
                                    client.sendMove(index);
                                }
                            }
                        } else {
                            System.out.println("Invalid command");
                        }
                }
            }
            client.close();

        } catch (
                UnknownHostException e) {
            System.out.println("Unknown host");
        } catch (
                SocketException e) {
            System.out.println("Socket not started");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}

