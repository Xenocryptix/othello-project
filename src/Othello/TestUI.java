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
        Game game = new OthelloGame();
        Player p1 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        Player p2 = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
        ((OthelloGame) game).setPlayer1(p1);
        ((OthelloGame) game).setPlayer1(p2);
        while (!game.isGameover()) {
            game.doMove(((ComputerPlayer) p1).determineMove(game));
            System.out.println(game.toString());
            game.doMove(((ComputerPlayer) p2).determineMove(game));
            System.out.println(game.toString());
        }
        System.out.println(((OthelloGame) game).getBoard().countDisk(Disk.BLACK));
        System.out.println(((OthelloGame) game).getBoard().countDisk(Disk.WHITE));
        System.out.println(game.getWinner());
    }
}
