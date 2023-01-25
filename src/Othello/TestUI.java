package Othello;

import Othello.model.Disk;
import Othello.model.Move;
import Othello.model.OthelloGame;
import Othello.model.OthelloMove;
import Othello.players.PlayerFactory;
import Othello.players.ai.ComputerPlayer;
import Othello.players.ai.GreedyStrategy;
import Othello.players.ai.NaiveStrategy;

public class TestUI {
    public static void main(String[] args) {
        OthelloGame game = new OthelloGame();
        ComputerPlayer p1 = new PlayerFactory().makeComputerPlayer(new NaiveStrategy());
        ComputerPlayer p2 = new PlayerFactory().makeComputerPlayer(new GreedyStrategy());
        game.setPlayer1(p1);
        game.setPlayer2(p2);
        while (!game.isGameover()) {
            Move move = p1.determineMove(game);
            System.out.println("Disk."+((OthelloMove) move).getDisk() + "," + ((OthelloMove) move).getCol() + "," + ((OthelloMove) move).getRow());
            game.doMove(move);
            move = p2.determineMove(game);
            System.out.println("Disk."+((OthelloMove) move).getDisk() + "," + ((OthelloMove) move).getCol() + "," + ((OthelloMove) move).getRow());
            game.doMove(move);
        }
        System.out.println(game.toString());
        System.out.println("BLACK has: " + game.deepCopy().countDisk(Disk.BLACK));
        System.out.println("WHITE has: " + game.deepCopy().countDisk(Disk.WHITE));
        System.out.println(game.getWinner().toString());
    }
}
