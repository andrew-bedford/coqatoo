package coqatoo;

import coqatoo.coq.Coqtop;
import coqatoo.coq.Proof;
import helpers.FileHelper;

import java.io.*;
import java.util.*;

public class Main {
    static final Map<String, List<String>> parameters = new HashMap<String, List<String>>();
    public static Coqtop coqtop;

    public static void main(String[] args) {
        coqtop = new Coqtop();
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
            String fileContents = FileHelper.convertFileToString(new File(filePath));

            //TODO Feed entire file, but record only the inputs/outputs relevant to the lemma/theorem given as argument
            Proof proof = new Proof(fileContents);
            System.out.println("---------------------------------------------");
            System.out.println("|             Coq Version                   |");
            System.out.println("---------------------------------------------");
            System.out.println(fileContents);

            System.out.println("---------------------------------------------");
            System.out.println("|             Text Version                  |");
            System.out.println("---------------------------------------------");
            System.out.println(proof.getTextVersion());


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
