package coqatoo;

import coqatoo.coq.Coqtop;
import coqatoo.rewriters.AnnotationRewriter;
import coqatoo.rewriters.PlainTextRewriter;
import helpers.FileHelper;

import java.io.*;
import java.util.*;

public class Main {
    static final Map<String, List<String>> parameters = new HashMap<String, List<String>>();
    public static Coqtop coqtop;
    public static Locale locale = new Locale("en"); //English is set as default locale

    public static void main(String[] args) {
        coqtop = new Coqtop();
        parseArguments(args);
        if (parameters.isEmpty() || parameters.containsKey("-help")) {
            System.out.println("Options:");
            System.out.println("-text [.v file] [lemma/theorem name]\t\t Converts the Coq proof of [lemma/theorem name] in file [file] to plain text.");
        }
        if (parameters.containsKey("-language")) {
            String language = parameters.get("-language").get(0);
            if (language.equals("en") || language.equals("fr")) {
                locale = new Locale(language);
            }
            else {
                System.err.println("Unsupported language. Coqatoo currently supports: en, fr.");
                System.exit(0);
            }

        }
        if (parameters.containsKey("-file")) {
            String filePath = parameters.get("-file").get(0);
            //String lemmaName = parameters.get("-text").get(1);

            verifyFileExists(filePath);
            //verifyLemmaIsPresentInFile(filePath, lemmaName);
            String fileContents = FileHelper.convertFileToString(new File(filePath));

            //TODO Feed entire file, but record only the inputs/outputs relevant to the lemma/theorem given as argument

            System.out.println("---------------------------------------------");
            System.out.println("|             Coq Version                   |");
            System.out.println("---------------------------------------------");
            System.out.println(fileContents);

            System.out.println("---------------------------------------------");
            System.out.println("|            Plain Text Version             |");
            System.out.println("---------------------------------------------");
            PlainTextRewriter plainTextRewriter = new PlainTextRewriter();
            plainTextRewriter.rewrite(fileContents);

            System.out.println("---------------------------------------------");
            System.out.println("|             Annotated Version             |");
            System.out.println("---------------------------------------------");
            AnnotationRewriter annotationRewriter = new AnnotationRewriter();
            //annotationRewriter.rewrite(fileContents);


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
