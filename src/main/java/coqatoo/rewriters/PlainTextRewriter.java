package coqatoo.rewriters;

import coqatoo.Main;
import coqatoo.coq.*;
import javafx.util.Pair;

import java.util.*;

import static java.lang.Thread.sleep;

public class PlainTextRewriter implements Rewriter {

    ResourceBundle rewritingBundle = ResourceBundle.getBundle("RewritingBundle", Main.locale);
    String _script;
    String _scriptWithUnfoldedAutos;
    List<Pair<Input, Output>> _inputsOutputs;

    private String generateScriptWithUnfoldedAutos(List<Pair<Input, Output>> inputsOutputs) {
        String scriptWithUnfoldedAutos = "";
        for(Pair<Input, Output> p : _inputsOutputs) {
            Input i = p.getKey();
            Output o = p.getValue();
            if (i.getType() == InputType.AUTO) {
                String[] tacticsUsedByAuto = o.getValue().split("\n");
                for (String s : tacticsUsedByAuto) {
                    if (!s.contains("(* info auto: *)")) { //Ignore the first line of the info_auto
                        scriptWithUnfoldedAutos += s.replace("simple ", "") + "\n"; //FIXME Temporary fix to transform the "simple apply" into "apply".
                    }
                }

            }
            else {
                scriptWithUnfoldedAutos += i.getValue() + "\n";
            }
        }
        return scriptWithUnfoldedAutos;
    }

    public Goal getProofGlobalGoal() {
        for(Pair<Input, Output> p : _inputsOutputs) {
            Input i = p.getKey();
            Output o = p.getValue();
            if (i.getType() == InputType.LEMMA) {
                return o.getGoal();
            }
        }

        return null;
    }

    public String getTextVersion() {
        String textVersion = "";
        String indentation = "";

        int i = 0;
        for(Pair<Input, Output> p : _inputsOutputs) {
            Input input = p.getKey();
            Output output = p.getValue();
            Output previousOutput = null;
            Set<Assumption> assumptionsBeforeTactic = new HashSet<>();
            Set<Assumption> assumptionsAddedAfterTactic = new HashSet<>();
            assumptionsAddedAfterTactic.addAll(output.getAssumptions());

            if (i != 0) {
                previousOutput = _inputsOutputs.get(i-1).getValue();
                assumptionsBeforeTactic.addAll(previousOutput.getAssumptions()); //TODO Cleaner
            }

            assumptionsAddedAfterTactic.removeAll(assumptionsBeforeTactic);

            switch (input.getType()) {
                case APPLY:
                    String lemmaName = input.getValue().split(" ")[1].replace(".", ""); //Obtains the "A" in "apply A."
                    String lemmaDefinition = "  ";
                    for (Assumption a : assumptionsBeforeTactic) {
                        if (a.getName().equals(lemmaName)) {
                            lemmaDefinition = a.getType();
                        }
                    }
                    //TODO Adapt output if definition is not of the form "A -> B"
                    int indexOfLastImplication = lemmaDefinition.lastIndexOf("->");
                    if (indexOfLastImplication != -1) {
                        textVersion += indentation;
                        textVersion += String.format(rewritingBundle.getString("apply")+"\n", lemmaDefinition, previousOutput.getGoal().toString(), lemmaDefinition.substring(0, indexOfLastImplication));
                    }
                    break;
                case ASSUMPTION:
                    textVersion += indentation;
                    textVersion += rewritingBundle.getString("assumption")+"\n";
                    break;
                case BULLET:
                    indentation = updatedIndentationLevel(input);
                    textVersion += indentation;
                    textVersion += String.format(rewritingBundle.getString("bullet")+"\n", input.getValue(), output.getGoal().toString());
                    indentation += "  ";
                    break;
                case DESTRUCT:
                    String destructedObject = input.getValue().substring(input.getValue().indexOf(" "), input.getValue().length()-1); //Obtains the "(A B)" in "destruct (A B)."
                    textVersion += String.format(rewritingBundle.getString("destruct")+"\n", destructedObject);
                    break;
                case INTRO:
                case INTROS:
                    textVersion += indentation;
                    for (Assumption a : assumptionsAddedAfterTactic) {
                        if (a.isOfKnownType()) {
                            textVersion += String.format(rewritingBundle.getString("intros.assume"), a.getName(), a.getType());
                        }
                        else {
                            textVersion += String.format(rewritingBundle.getString("intros.suppose"), a.getType());
                        }
                    }

                    textVersion += String.format(rewritingBundle.getString("intros.goal")+"\n", output.getGoal().toString());
                    break;
                case INTUITION:
                    textVersion += String.format(rewritingBundle.getString("intuition")+"\n", previousOutput.getGoal().toString());
                    break;
                case INVERSION:
                    textVersion += indentation;
                    String inversionLemmaName = input.getValue().split(" ")[1].replace(".", ""); //Obtains the "A" in "apply A."
                    String inversionLemmaDefinition = "";
                    for (Assumption a : assumptionsBeforeTactic) {
                        if (a.getName().equals(inversionLemmaName)) {
                            inversionLemmaDefinition = a.getType();
                        }
                    }

                    String enumerationOfAddedAssumptions = "";
                    for (Assumption a : assumptionsAddedAfterTactic) {
                        if (!a.isOfKnownType()) {
                            enumerationOfAddedAssumptions += a.getType() + ", ";
                        }
                    }
                    enumerationOfAddedAssumptions = enumerationOfAddedAssumptions.substring(0, enumerationOfAddedAssumptions.length()-2); //Remove the last ", "

                    textVersion += String.format(rewritingBundle.getString("inversion")+"\n", inversionLemmaDefinition, enumerationOfAddedAssumptions);
                    break;
                case LEMMA:
                    textVersion += input.getValue() + "\n";
                    break;
                case OMEGA:
                    textVersion += rewritingBundle.getString("omega")+"\n";
                    break;
                case PROOF:
                    textVersion += input.getValue() + "\n";
                    break;
                case REFLEXIVITY:
                    textVersion += rewritingBundle.getString("reflexivity")+"\n";
                    break;
                case SIMPL: //TODO "simpl in ..."
                    textVersion += String.format(rewritingBundle.getString("simpl")+"\n", previousOutput.getGoal().toString(), output.getGoal().toString());
                    break;
                case SPLIT:
                    break;
                case UNFOLD:
                    String unfoldedDefinition = input.getValue().split(" ")[1].replace(".", ""); //Obtains the "A" in "unfold A."
                    textVersion += String.format(rewritingBundle.getString("unfold")+"\n", unfoldedDefinition, output.getGoal().toString());
                    break;
                case QED:
                    textVersion += "Qed\n";
                    break;
                default:
                    break;
            }

            i++;
        }

        return textVersion;
    }

    private String updatedIndentationLevel(Input input) {
        //Assumes that the input is of type BULLET
        if (input.getType() == InputType.BULLET) {
            int indentationLevel = input.getValue().split(" ")[0].length(); //The bullet length determines the indendation level (e.g., - = 1, -- = 2, --- = 3)
            String indentation = "";
            for (int i = 1; i <= indentationLevel; i++) {
                indentation += "  ";
            }
            return indentation;
        }

        return "";
    }


    @Override
    public void rewrite(String proofScript) {
       String formattedScript = formatScript(proofScript);
       //extractInformation(proofScript);

       //System.out.println(getTextVersion());
    }

    private String formatScript(String proofScript) {
        String formattedScript = proofScript;

        //Step 1: Format proof so that there is one tactic/chain per line
        formattedScript = formattedScript.replaceAll("\\.", "\\.\n");

        //Step 2: Remove bullets
        String[] lines = formattedScript.split("\n");
        formattedScript = "";
        for(String line : lines) {
            String l = line.trim();
            while (l.startsWith("-") || l.startsWith("*") || l.startsWith("+") || l.startsWith("{") || l.startsWith("}")) {
                l = l.substring(1, l.length()).trim();
            }
            if (!l.equals("")) {
                formattedScript += l + "\n";
            }
        }

        //Step 3: Execute formatted script to get the list of inputs/outputs
        _inputsOutputs = Main.coqtop.execute(formattedScript);

        //Step 4: Build the proof tree
        System.out.println("---------------------------------------------");
        System.out.println("|                Proof Tree                 |");
        System.out.println("---------------------------------------------");
        System.out.println("digraph {");
        Stack<String> s = new Stack<>();
        int i = 0;
        for(Pair<Input,Output> p : _inputsOutputs) {
            if (p.getKey().getValue().equals("Qed.")) { break; }
            if (i == 0) {
                s.push(String.format("%d. %s", i, p.getKey().getValue()));
            }
            else if (i > 0) {
                String previousNodeName = s.pop();
                //if (!s.peek().isEmpty()) { previousNodeName = s.pop(); }

                Pair<Input, Output> previousPair = _inputsOutputs.get(i-1);
                int numberOfSubgoalsBeforeTactic = previousPair.getValue().getNumberOfRemainingSubgoals();
                int numberOfSubgoalsAfterTactic = p.getValue().getNumberOfRemainingSubgoals();

                int addedSubgoals = numberOfSubgoalsAfterTactic - numberOfSubgoalsBeforeTactic;
                if (addedSubgoals > 0) {
                    for(int j=0; j<=addedSubgoals; j++) {
                        s.push(String.format("%d. %s", i, p.getKey().getValue()));
                    }
                    System.out.println(String.format("\"%s\" -> \"%d. %s\";", previousNodeName, i, p.getKey().getValue()));
                }
                else if (addedSubgoals == 0) {
                    System.out.println(String.format("\"%s\" -> \"%d. %s\";", previousNodeName, i, p.getKey().getValue()));
                    s.push(String.format("%d. %s", i, p.getKey().getValue()));
                }
                else if (addedSubgoals < 0) {
                    System.out.println(String.format("\"%s\" -> \"%d. %s\";", previousNodeName, i, p.getKey().getValue()));
                }


            }
            i++;
        }
        System.out.println("}");


        //System.out.println(formattedScript);
        return formattedScript;

    }

    private void extractInformation(String proofScript) {
        _script = proofScript;
        _inputsOutputs = Main.coqtop.execute(_script);

        _scriptWithUnfoldedAutos = generateScriptWithUnfoldedAutos(_inputsOutputs);
        if (!_scriptWithUnfoldedAutos.equals(_script)) {
            Coqtop coqtop = new Coqtop();
            _inputsOutputs = coqtop.execute(_scriptWithUnfoldedAutos);
        }
    }
}
