package othello.controller.client;

/**
 * Listener interface to be used to forward messages between the client and TUI.
 */
public interface Listener {
    /**
     * Prints out the message to the TUI.
     *
     * @param message The message to be printed out
     */
    void printMessage(String message);
}
