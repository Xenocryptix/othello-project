package othello.view;

import javax.sound.sampled.*;
import java.io.File;
import java.io.IOException;

/**
 * Responsible for creating a sound effect from a WAV file.
 */
public class SoundEffect {
    private Clip clip;

    /**
     * Initialises the class with the file path of the sound.
     * file
     *
     * @param path The file path of the file
     */
    public SoundEffect(String path) {
        AudioInputStream sound = null;
        try {
            File file = new File(path);
            sound = AudioSystem.getAudioInputStream(file);
            clip = AudioSystem.getClip();
            clip.open(sound);
        } catch (UnsupportedAudioFileException e) {
            System.out.println("This file format can not be used");
        } catch (IOException e) {
            System.out.println("Error in reading the file");
        } catch (LineUnavailableException e) {
            System.out.println("The line can not be opened");
        }
    }

    /**
     * Plays the sound.
     */
    public void play() {
        clip.setFramePosition(0);
        clip.start();
    }
}
