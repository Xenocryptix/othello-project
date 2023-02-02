## Othello
The full package for playing Othello

## Compatibility
The TUI uses emoji characters to display the board, therefore it's advisable to run the file using Windows Terminal, as Command Prompt may not support these characters

## Usage

* Where to find the files
All executable files can be located in Othello main folder

* Running executable files
All executable files are in the .jar format. Here's the steps to run them:
- On the folder containing the files, locate to the search bar at the top and type "cmd"
- An alternate way is to open Command Prompt/Terminal then locate to the folder using "cd"
- Type in "java -jar <filename>.jar" (make sure that the terminal is located to the folder containing the file)

* Hosting a server:
You can host a server using Server.jar file. When asked to input, type in a valid port number. A server will be initialized in localhost at the specified port number

* Using the OthelloTUI:
You'll first be asked to input the server IP address (localhost if you want to connect to your own local server), then the port number. After that, input your username to log in to the server. You'll then see the list of commands available that you can use.
To play a game, you must first queue by type "queue". After the server found a match, the TUI will print a message and print out the state of the board. When it's your turn, you do a move by typing a letter followed by a number (for example: A1, B4)

## Testing
You can find test files inside the "test" package. GameLogicTest contains the test for game logic classes, while NetworkingTest contains the test for server and client related classes.

## Version
Language level: Java 11

## Contributing
Moamen Elkayal
Minh Hieu Chu