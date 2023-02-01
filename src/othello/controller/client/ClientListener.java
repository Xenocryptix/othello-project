package othello.controller.client;

/**
 * Responsible for forwarding messages to the TUI.
 */
public class ClientListener implements Listener {
    /**
     * Prints out the message to the TUI.
     *
     * @param message The message to be printed out
     */
    @Override
    public void printMessage(String message) {
        System.out.println(message);
    }
}
