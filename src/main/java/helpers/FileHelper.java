package helpers;

import java.io.File;
import java.nio.file.Files;

public class FileHelper {
    public static boolean fileExists(String filePath) {
        File f = new File(filePath);
        return f.exists();
    }

    public static String convertFileToString(File file) {
        try {
            byte[] bytes = Files.readAllBytes(file.toPath());
            String contents =  new String(bytes,"UTF-8");
            return contents;
        }
        catch (Exception e) {
            e.printStackTrace();
            return "";
        }
    }
}
