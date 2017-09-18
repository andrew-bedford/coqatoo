package coqatoo;

import helpers.FileHelper;

import java.io.*;
import java.util.*;

public class Main {
    static final Map<String, List<String>> parameters = new HashMap<String, List<String>>();

    public static void main(String[] args) {
        parseArguments(args);
        if (parameters.isEmpty() || parameters.containsKey("-help")) {
            System.out.println("Options:");
            System.out.println("-text [.v file] [lemma/theorem name]\t\t Converts the Coq proof of [lemma/theorem name] in file [file] to text (i.e., classical proof).");
        }
        else if (parameters.containsKey("-text")) {
            String filePath = parameters.get("-text").get(0);
            String lemmaName = parameters.get("-text").get(1);

            verifyFileExists(filePath);
            verifyLemmaIsPresentInFile(filePath, lemmaName);

            String fileContents = FileHelper.convertFileToString(new File(filePath));
            String[] fileLines = fileContents.split("\n");
            try {
                //Note: "coqtop < file" feeds the whole contents of file to coqtop automatically, but we need to execute it line by line
                ProcessBuilder processBuilder = new ProcessBuilder("coqtop");
                Process process = processBuilder.start();

                OutputStream stdin = process.getOutputStream();
                InputStream stdout = process.getInputStream();

                BufferedReader reader = new BufferedReader(new InputStreamReader(stdout));
                BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(stdin));
                String coqtopOutput = "";

                for (String s : fileLines) {

                    while (reader.ready()) {
                        coqtopOutput = reader.readLine();
                        System.out.println(coqtopOutput);
                    }
                    writer.write(s+"\n");
                    writer.flush();
                }
                reader.close();
                writer.close();
            }
            catch (Exception e) { e.printStackTrace(); }

        }
    }

    private static void verifyLemmaIsPresentInFile(String filePath, String lemmaName) {
        String fileContents = FileHelper.convertFileToString(new File(filePath));
        if (!fileContents.contains(lemmaName)) {
            System.err.println("Error: The file '"+filePath+"' does not seem to contain a lemma/theorem/example named '"+lemmaName+"'");
            System.exit(1);
        }
    }

    private static void verifyFileExists(String filePath) {
        if (!FileHelper.fileExists(filePath)) {
            System.err.println("Error: File '"+filePath+"' not found.");
            System.exit(1);
        }
    }

    private static void parseArguments(String[] args) {
        List<String> options = null;
        for (int i = 0; i < args.length; i++) {
            final String a = args[i];

            if (a.charAt(0) == '-') {
                if (a.length() < 2) {
                    System.err.println("Error at argument " + a);
                    return;
                }

                options = new ArrayList<String>();
                parameters.put(a.substring(1), options);
            }
            else if (options != null) {
                options.add(a);
            }
            else {
                System.err.println("Illegal parameter usage");
                return;
            }
        }
    }
}
