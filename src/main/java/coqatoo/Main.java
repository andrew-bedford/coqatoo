package coqatoo;

import coqatoo.coq.Input;
import coqatoo.coq.Output;
import helpers.FileHelper;
import javafx.util.Pair;

import java.io.*;
import java.util.*;

import static java.lang.Thread.sleep;

public class Main {
    static final Map<String, List<String>> parameters = new HashMap<String, List<String>>();

    public static void main(String[] args) {
        parseArguments(args);
        if (parameters.isEmpty() || parameters.containsKey("-help")) {
            System.out.println("Options:");
            System.out.println("-text [.v file] [lemma/theorem name]\t\t Converts the Coq proof of [lemma/theorem name] in file [file] to plain text.");
        }
        else if (parameters.containsKey("-text")) {
            String filePath = parameters.get("-text").get(0);
            String lemmaName = parameters.get("-text").get(1);

            verifyFileExists(filePath);
            verifyLemmaIsPresentInFile(filePath, lemmaName);

            //TODO Regroup the mapping of inputs to outputs in a single function
            String fileContents = FileHelper.convertFileToString(new File(filePath));
            String[] fileLines = fileContents.split("\n");
            try {
                //Note: "coqtop < file" feeds the whole contents of file to coqtop automatically, but we need to execute it line by line
                ProcessBuilder processBuilder = new ProcessBuilder("coqtop");
                Process process = processBuilder.start();

                OutputStream stdin = process.getOutputStream();
                InputStream stdout = process.getInputStream();
                InputStream stderr = process.getErrorStream(); //TODO Output coqtop errors

                BufferedReader reader = new BufferedReader(new InputStreamReader(stdout));
                BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(stdin));
                reader.readLine(); //Ignore the first output of coqtop

                List<Pair<Input, Output>> inputsToOutputs = new ArrayList<>();

                //TODO Feed entire file, but record only the inputs/outputs relevant to the lemma/theorem given as argument
                for (String input : fileLines) {
                    writer.write(input+"\n");
                    writer.flush();

                    String output = "";
                    while (!reader.ready()) {
                        sleep(1);
                    }

                    while (reader.ready()) {
                        output += reader.readLine() + "\n";

                    }
                    inputsToOutputs.add(new Pair<>(new Input(input), new Output(output)));
                    System.out.println(input);
                    System.out.println(output);

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
