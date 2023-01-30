package Othello.Client;

import javax.sound.sampled.*;
import java.io.File;
import java.io.IOException;

public class SoundEffect {
    private Clip clip;

    public void setFile(String fileName) {
        File file = new File(fileName);
        AudioInputStream sound = null;
        try {
            sound = AudioSystem.getAudioInputStream(file);
            clip = AudioSystem.getClip();
            clip.open(sound);
        } catch (UnsupportedAudioFileException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        } catch (LineUnavailableException e) {
            throw new RuntimeException(e);
        }
    }
    public void play() {
        clip.setFramePosition(0);
        clip.start();
    }
}
