package Othello.client;

import java.io.*;
import java.net.InetAddress;
import java.net.SocketException;
import java.net.UnknownHostException;
import java.util.*;

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

        OthelloClient client = new OthelloClient();
        try {
            connected = client.connect(InetAddress.getByName(serverAddress), port);
            if (!connected) {
                throw new SocketException();
            }

            client.sendHello("desc");
            System.out.print("Enter username: ");
            username = input.readLine();
            client.sendLogin(username);
            System.out.println("Enter command: ");
            command = input.readLine();

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
                command = input.readLine();
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
