package coqatoo.rewriters;

import coqatoo.Main;
import coqatoo.coq.*;
import javafx.util.Pair;
import java.util.*;

public class AnnotationRewriter implements Rewriter {

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
                        textVersion += "(* ";
                        textVersion += String.format(rewritingBundle.getString("apply"), lemmaDefinition, previousOutput.getGoal().toString(), lemmaDefinition.substring(0, indexOfLastImplication));
                        textVersion += "*) ";
                        textVersion += input.getValue()+"\n";
                    }
                    else {
                        textVersion += indentation;
                        textVersion += input.getValue()+"\n";
                    }
                    break;
                case ASSUMPTION:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += rewritingBundle.getString("assumption");
                    textVersion += "*) ";
                    textVersion += input.getValue()+"\n";
                    break;
                case BULLET:
                    indentation = updatedIndentationLevel(input);
                    textVersion += indentation;
                    textVersion += input.getValue();
                    textVersion += " (* ";
                    textVersion += String.format(rewritingBundle.getString("bullet"), "", output.getGoal().toString());
                    textVersion += " *)\n";
                    indentation += "  ";
                    break;
                case DESTRUCT:
                    String destructedObject = input.getValue().substring(input.getValue().indexOf(" "), input.getValue().length()-1); //Obtains the "(A B)" in "destruct (A B)."
                    textVersion += "(* ";
                    textVersion += String.format(rewritingBundle.getString("destruct"), destructedObject);
                    textVersion += "*) ";
                    textVersion += input.getValue()+"\n";
                    break;
                case INTRO:
                case INTROS:
                    textVersion += indentation;
                    textVersion += "(* ";
                    for (Assumption a : assumptionsAddedAfterTactic) {
                        if (a.isOfKnownType()) {
                            textVersion += String.format(rewritingBundle.getString("intros.assume"), a.getName(), a.getType());
                        }
                        else {
                            textVersion += String.format(rewritingBundle.getString("intros.suppose"), a.getType());
                        }
                    }

                    textVersion += String.format(rewritingBundle.getString("intros.goal"), output.getGoal().toString());
                    textVersion += "*) ";
                    textVersion += input.getValue()+"\n";
                    break;
                case INTUITION:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += String.format(rewritingBundle.getString("intuition"), previousOutput.getGoal().toString());
                    textVersion += " *)";
                    textVersion += input.getValue()+"\n";
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

                    textVersion += "(* ";
                    textVersion += String.format(rewritingBundle.getString("inversion"), inversionLemmaDefinition, enumerationOfAddedAssumptions);
                    textVersion += " *)";
                    textVersion += input.getValue()+"\n";
                    break;
                case LEMMA:
                    textVersion += input.getValue() + "\n";
                    break;
                case OMEGA:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += rewritingBundle.getString("omega");
                    textVersion += " *)";
                    textVersion += input.getValue()+"\n";
                    break;
                case PROOF:
                    textVersion += input.getValue() + "\n";
                    break;
                case REFLEXIVITY:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += rewritingBundle.getString("reflexivity");
                    textVersion += " *)";
                    textVersion += input.getValue()+"\n";
                    break;
                case SIMPL: //TODO "simpl in ..."
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += String.format(rewritingBundle.getString("simpl"), previousOutput.getGoal().toString(), output.getGoal().toString());
                    textVersion += " *)";
                    textVersion += input.getValue()+"\n";
                    break;
                case SPLIT:
                    textVersion += indentation;
                    textVersion += input.getValue() + "\n";
                    break;
                case UNFOLD:
                    textVersion += indentation;
                    String unfoldedDefinition = input.getValue().split(" ")[1].replace(".", ""); //Obtains the "A" in "unfold A."
                    textVersion += "(* ";
                    textVersion += String.format(rewritingBundle.getString("unfold"), unfoldedDefinition, output.getGoal().toString());
                    textVersion += " *)";
                    textVersion += input.getValue()+"\n";
                    break;
                case QED:
                    textVersion += input.getValue() + "\n";
                    break;
                default:
                    textVersion += indentation;
                    textVersion += input.getValue() + "\n";
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

        System.out.println(getTextVersion());
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
        //TODO Clean this part
        Stack<Integer> s = new Stack<>();
        Map<Integer, String> bulletLevel = new HashMap<>();
        Map<Integer, String> bulletsToAddAfter = new HashMap<>();
        String bulletStr = "";
        int i = 0;
        for(Pair<Input,Output> p : _inputsOutputs) {
            if (p.getKey().getValue().equals("Qed.")) { break; }
            if (i == 0) {
                s.push(i);
            }
            else if (i > 0) {
                Integer previousNode = s.pop();

                Pair<Input, Output> previousPair = _inputsOutputs.get(i-1);
                int numberOfSubgoalsBeforeTactic = previousPair.getValue().getNumberOfRemainingSubgoals();
                int numberOfSubgoalsAfterTactic = p.getValue().getNumberOfRemainingSubgoals();

                int addedSubgoals = numberOfSubgoalsAfterTactic - numberOfSubgoalsBeforeTactic;
                if (addedSubgoals > 0) {
                    for(int j=0; j<=addedSubgoals; j++) {
                        s.push(i);
                    }
                    bulletStr += "-";
                    bulletLevel.put(i, bulletStr);
                }
                else if (addedSubgoals == 0) {
                    if (bulletLevel.get(previousNode) != null) {
                        bulletsToAddAfter.put(i, bulletLevel.get(previousNode));
                    }
                    s.push(i);
                }
                else if (addedSubgoals < 0) {
                    if (bulletLevel.get(previousNode) != null) {
                        bulletsToAddAfter.put(i, bulletLevel.get(previousNode));
                    }
                    if (!s.empty()) {
                        int nextNodeId = s.peek();
                        bulletStr = bulletLevel.get(nextNodeId);
                    }
                }
            }
            i++;
        }

        //Step 5: Insert bullets in _inputsOutputs
        int numberOfInputsInserted = 0;
        for(Integer index : bulletsToAddAfter.keySet()) {
            _inputsOutputs.add(index+numberOfInputsInserted, new Pair(new Input(bulletsToAddAfter.get(index)), _inputsOutputs.get(index+numberOfInputsInserted-1).getValue()));
            numberOfInputsInserted++;
        }

        return formattedScript;

    }

    public void outputProofTreeAsDot() {
        System.out.println("---------------------------------------------");
        System.out.println("|                Proof Tree                 |");
        System.out.println("---------------------------------------------");
        System.out.println("digraph {");
        Stack<Integer> s = new Stack<>();
        Map<Integer, String> bulletLevel = new HashMap<>();
        Map<Integer, String> bulletsToAddAfter = new HashMap<>();
        String bulletStr = "";
        int i = 0;
        for(Pair<Input,Output> p : _inputsOutputs) {
            if (p.getKey().getValue().equals("Qed.")) { break; }
            if (i == 0) {
                s.push(i);
            }
            else if (i > 0) {
                Integer previousNode = s.pop();

                Pair<Input, Output> previousPair = _inputsOutputs.get(i-1);
                int numberOfSubgoalsBeforeTactic = previousPair.getValue().getNumberOfRemainingSubgoals();
                int numberOfSubgoalsAfterTactic = p.getValue().getNumberOfRemainingSubgoals();

                int addedSubgoals = numberOfSubgoalsAfterTactic - numberOfSubgoalsBeforeTactic;
                if (addedSubgoals > 0) {
                    for(int j=0; j<=addedSubgoals; j++) {
                        s.push(i);
                    }
                    System.out.println(String.format("\"%d. %s\" -> \"%d. %s\";", previousNode, _inputsOutputs.get(previousNode).getKey().getValue(), i, _inputsOutputs.get(i).getKey().getValue()));
                    bulletStr += "-";
                    bulletLevel.put(i, bulletStr);
                }
                else if (addedSubgoals == 0) {
                    if (bulletLevel.get(previousNode) != null) {
                        bulletsToAddAfter.put(i, bulletLevel.get(previousNode));
                    }
                    System.out.println(String.format("\"%d. %s\" -> \"%d. %s\";", previousNode, _inputsOutputs.get(previousNode).getKey().getValue(), i, _inputsOutputs.get(i).getKey().getValue()));
                    s.push(i);
                }
                else if (addedSubgoals < 0) {
                    if (bulletLevel.get(previousNode) != null) {
                        bulletsToAddAfter.put(i, bulletLevel.get(previousNode));
                    }
                    System.out.println(String.format("\"%d. %s\" -> \"%d. %s\";", previousNode, _inputsOutputs.get(previousNode).getKey().getValue(), i, _inputsOutputs.get(i).getKey().getValue()));
                    if (!s.empty()) {
                        int nextNodeId = s.peek();
                        bulletStr = bulletLevel.get(nextNodeId);
                    }
                }
            }
            i++;
        }
        System.out.println("}");
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
