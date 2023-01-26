package Othello.client;

import java.io.*;
import java.net.InetAddress;
import java.net.SocketException;
import java.net.UnknownHostException;
import java.util.*;

public class OthelloTUI {
    public static void main(String[] args) {
        String serverAddress, username, command;
        boolean connected;
        int port;
        Scanner input = new Scanner(System.in);
        System.out.print("Enter a server address: ");
        serverAddress = input.nextLine();
        System.out.print("Enter port number: ");
        port = input.nextInt();
        if (port < 0 || port > 65536) {
            throw new NumberFormatException();
        }
        OthelloClient client = new OthelloClient();
        PipedReader inputStream;
        try {
            inputStream = new PipedReader(client.getPipedWriter());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        try {
            connected = client.connect(InetAddress.getByName(serverAddress), port);
            if (!connected) {
                throw new SocketException();
            }
            client.sendHello("desc");
            new Thread(client).start();
            System.out.println(inputStream.read());

            System.out.print("Enter username: ");
            username = input.nextLine();

            client.sendLogin(username);

            String logged = String.valueOf(inputStream.read());
            System.out.println(inputStream.read());

            System.out.println("Enter command: ");
            command = input.nextLine();

            //TODO: HELP MENU


            while (!Objects.equals(command, "quit")) {
                switch (command) {
                    case "queue":
                        client.queue();
                        //TODO: WAIT
                        break;
                    case "list":
                        client.sendList();
                        break;
                    //TODO: command

                }
                command = input.nextLine();
            }
            client.close();
        } catch (UnknownHostException e) {
            System.out.println("Unknown host");
        } catch (SocketException e) {
            System.out.println("Socket not started");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }
}
