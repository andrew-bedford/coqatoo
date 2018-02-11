package coqatoo;

import coqatoo.coq.Coqtop;
import coqatoo.rewriters.CoqRewriter;
import coqatoo.rewriters.LatexRewriter;
import coqatoo.rewriters.TextRewriter;
import helpers.FileHelper;

import java.io.*;
import java.util.*;

public class Main {
    static final Map<String, List<String>> parameters = new HashMap<String, List<String>>();
    public static Coqtop coqtop;
    public static Locale locale = new Locale("en"); //English is set as default locale
    public static Boolean debug = false;

    public static void main(String[] args) {
        coqtop = new Coqtop();
        parseArguments(args);
        if (parameters.isEmpty() || parameters.containsKey("-help")) {
            System.out.println("Options:");
            System.out.println("--debug                                        Display debugging information");
            System.out.println("--input [.v file]                              File containing the Coq proof");
            System.out.println("--language [en (default) | fr]                 Target language");
            System.out.println("--mode [text (default) | coq | latex | dot]    Output mode");
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
        if (parameters.containsKey("-debug")) {
            debug = true;
        }
        if (parameters.containsKey("-input")) {
            String filePath = parameters.get("-input").get(0);

            verifyFileExists(filePath);
            String fileContents = FileHelper.convertFileToString(new File(filePath));

            //TODO Feed entire file, but record only the inputs/outputs relevant to the lemma/theorem given as argument

            System.out.println("---------------------------------------------");
            System.out.println("|             Coq Version                   |");
            System.out.println("---------------------------------------------");
            System.out.println(fileContents);



            if (parameters.containsKey("-mode")) {
                String mode = parameters.get("-mode").get(0);

                TextRewriter textRewriter = new TextRewriter();

                switch (mode) {
                    case "coq":
                        System.out.println("---------------------------------------------");
                        System.out.println("|                Coq Version                |");
                        System.out.println("---------------------------------------------");
                        CoqRewriter coqRewriter = new CoqRewriter();
                        coqRewriter.rewrite(fileContents);
                        break;
                    case "latex":
                        System.out.println("---------------------------------------------");
                        System.out.println("|              LaTeX Version                |");
                        System.out.println("---------------------------------------------");
                        LatexRewriter latexRewriter = new LatexRewriter();
                        latexRewriter.rewrite(fileContents);
                        break;
                    case "dot":
                        textRewriter.rewrite(fileContents);
                        textRewriter.outputProofTreeAsDot();
                        break;
                    default: //Plain text is the default output mode
                        System.out.println("---------------------------------------------");
                        System.out.println("|               Text Version                |");
                        System.out.println("---------------------------------------------");
                        textRewriter.rewrite(fileContents);
                        break;
                }

            }
            else { //Plain text is the default output mode
                System.out.println("---------------------------------------------");
                System.out.println("|            Plain Text Version             |");
                System.out.println("---------------------------------------------");
                TextRewriter textRewriter = new TextRewriter();
                textRewriter.rewrite(fileContents);
            }


            coqtop.stop();
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
