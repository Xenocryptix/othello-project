package Othello;

import Othello.model.Disk;
import Othello.model.Game;
import Othello.model.OthelloGame;
import Othello.players.ai.ComputerPlayer;
import Othello.players.ai.GreedyStrategy;
import Othello.players.ai.NaiveStrategy;
import Othello.players.PlayerFactory;
import Othello.players.Player;

public class TestUI {
    public static void main(String[] args) {
        OthelloGame game = new OthelloGame();
        ComputerPlayer p1 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        ComputerPlayer p2 = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
        game.setPlayer1(p1);
        game.setPlayer2(p2);
        while (!game.isGameover()) {
            game.doMove(p1.determineMove(game));
            System.out.println(game.toString());
            game.doMove(p2.determineMove(game));
            System.out.println(game.toString());
        }
        System.out.println("BLACK has: " + game.getBoard().countDisk(Disk.BLACK));
        System.out.println("WHITE has: " + game.getBoard().countDisk(Disk.WHITE));
        System.out.println(game.getWinner().toString());
    }
}
