package Othello;

import Othello.players.ai.ComputerPlayer;
import Othello.players.ai.GreedyStrategy;
import Othello.players.ai.NaiveStrategy;
import Othello.players.PlayerFactory;
import Othello.players.Player;

public class test {
    public static void main(String[] args) {
        Game game = new OthelloGame();
        Player p1 = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
        Player p2 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        ((OthelloGame) game).setPlayer1(p1);
        ((OthelloGame) game).setPlayer1(p2);
        System.out.println(game);
        while (!game.isGameover()) {
            game.doMove(((ComputerPlayer) p1).determineMove(game));
            System.out.println(game);
            game.doMove(((ComputerPlayer) p2).determineMove(game));
            System.out.println(game);
        }

    }
}
