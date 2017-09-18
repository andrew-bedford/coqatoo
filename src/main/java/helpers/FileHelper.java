package helpers;

import java.io.File;

public class FileHelper {
    public static boolean fileExists(String filePath) {
        File f = new File(filePath);
        return f.exists();
    }
}
