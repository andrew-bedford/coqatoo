package coqatoo.rewriters;

import coqatoo.Main;
import coqatoo.coq.*;
import helpers.SetHelper;

import java.util.*;

public class PlainTextRewriter implements Rewriter {

    ResourceBundle rewritingBundle = ResourceBundle.getBundle("RewritingBundle", Main.locale);
    String _script;
    String _scriptWithUnfoldedAutos;
    List<InputOutput> _inputsOutputs;

    private String generateScriptWithUnfoldedAutos(List<InputOutput> inputsOutputs) {
        String scriptWithUnfoldedAutos = "";
        for(InputOutput p : _inputsOutputs) {
            Input i = p.getInput();
            Output o = p.getOutput();
            if (i.getType() == InputType.AUTO) {
                String[] tacticsUsedByAuto = o.getValue().split("\n");
                for (String s : tacticsUsedByAuto) {
                    if (!s.contains("(* info auto: *)")) { //Ignore the first line of the info_auto
                        scriptWithUnfoldedAutos += s.replace("simple ", "") + "\n"; //FIXME Temporary fix to transform the "simple apply" into "apply".
                    }
                }

            }
            else {
                scriptWithUnfoldedAutos += i.toString() + "\n";
            }
        }
        return scriptWithUnfoldedAutos;
    }

    public Goal getProofGlobalGoal() {
        for(InputOutput p : _inputsOutputs) {
            Input i = p.getInput();
            Output o = p.getOutput();
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
        for(InputOutput p : _inputsOutputs) {
            Input input = p.getInput();
            Output output = p.getOutput();
            Output previousOutput = null;
            Set<Assumption> assumptionsBeforeTactic = new HashSet<>();
            Set<Assumption> assumptionsAddedAfterTactic = new HashSet<>();
            assumptionsAddedAfterTactic.addAll(output.getAssumptions());

            if (i != 0) {
                previousOutput = _inputsOutputs.get(i-1).getOutput();
                assumptionsBeforeTactic.addAll(previousOutput.getAssumptions()); //TODO Cleaner
            }

            assumptionsAddedAfterTactic.removeAll(assumptionsBeforeTactic);

            switch (input.getType()) {
                case APPLY:
                    String lemmaName = input.toString().split(" ")[1].replace(".", ""); //Obtains the "A" in "apply A."
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
                        String[] propositionsLeftToProve = lemmaDefinition.substring(0, indexOfLastImplication).split("->");
                        Arrays.stream(propositionsLeftToProve).map(String::trim).toArray(unused -> propositionsLeftToProve); //Removes whitespace from all elements of the array
                        String commaSeparatedPropositionsLeftToProve = String.join(", ", propositionsLeftToProve);
                        textVersion += String.format(rewritingBundle.getString("apply")+"\n", lemmaDefinition, previousOutput.getGoal().toString(), commaSeparatedPropositionsLeftToProve);
                    }
                    break;
                case ASSUMPTION:
                    textVersion += indentation;
                    textVersion += rewritingBundle.getString("assumption")+"\n";
                    break;
                case BULLET:
                    indentation = updatedIndentationLevel(input);
                    textVersion += indentation;
                    textVersion += String.format(rewritingBundle.getString("bullet")+"\n", input.toString(), "<["+output.getGoal().toString()+"]>");
                    indentation += "  ";
                    break;
                case DESTRUCT:
                    textVersion += indentation;
                    String destructedObject = input.toString().substring(input.toString().indexOf(" "), input.toString().length()-1); //Obtains the "(A B)" in "destruct (A B)."
                    textVersion += String.format(rewritingBundle.getString("destruct")+"\n", destructedObject);
                    break;
                case INTRO:
                case INTROS:
                    textVersion += indentation;

                    String variables = "";
                    String variableNames = "";
                    String variablesTypes = "";
                    String hypotheses = "";
                    Map<String, Set<String>> typesToVariables = new HashMap<>();

                    for (Assumption a : assumptionsAddedAfterTactic) {
                        // To choose whether the rule intros.given or intros.suppose should be used, we need to determine the type of the current assumption.
                        Boolean assumptionTypeIsAlsoVariableName = false;
                        for (Assumption b : SetHelper.union(assumptionsBeforeTactic, assumptionsAddedAfterTactic)) {
                            if (a.getType().equals(b.getName())) {
                                assumptionTypeIsAlsoVariableName = true;
                            }
                        }

                        if (!a.typeContainsSpaces() && !assumptionTypeIsAlsoVariableName) {
                            // Need to use intros.given
                            Set<String> variablesWithSameType = typesToVariables.getOrDefault(a.getType(), new HashSet<String>());
                            variablesWithSameType.add(a.getName());
                            typesToVariables.put(a.getType(), variablesWithSameType);
                        }
                        else {
                            // Need to use intros.suppose
                            hypotheses += String.format("<[%s]>, ", a.getType());
                        }
                    }

                    for (String type : typesToVariables.keySet()) {
                        Set<String> variablesWithSameType = typesToVariables.get(type);
                        variables += String.format("<[%s : %s]>, ", SetHelper.toString(variablesWithSameType), type);

                    }

                    textVersion += "<line>";
                    if (!variables.isEmpty()) {
                        variables = variables.substring(0, variables.length() - 2);
                        textVersion += String.format(rewritingBundle.getString("intros.given"), variables);
                    }
                    if (!hypotheses.isEmpty()) {
                        hypotheses = hypotheses.substring(0, hypotheses.length() - 2);
                        textVersion += String.format(rewritingBundle.getString("intros.suppose"), hypotheses);
                    }
                    textVersion += String.format(rewritingBundle.getString("intros.goal")+"</line>\n", "<["+output.getGoal().toString()+"]>");
                    break;
                case INTUITION:
                    textVersion += indentation;
                    textVersion += String.format(rewritingBundle.getString("intuition")+"\n", previousOutput.getGoal().toString());
                    break;
                case INVERSION:
                    textVersion += indentation;
                    String inversionLemmaName = input.toString().split(" ")[1].replace(".", ""); //Obtains the "A" in "apply A."
                    String inversionLemmaDefinition = "";
                    for (Assumption a : assumptionsBeforeTactic) {
                        if (a.getName().equals(inversionLemmaName)) {
                            inversionLemmaDefinition = a.getType();
                        }
                    }

                    String enumerationOfAddedAssumptions = "";
                    for (Assumption a : assumptionsAddedAfterTactic) {
                        if (!a.typeContainsSpaces()) {
                            enumerationOfAddedAssumptions += a.getType() + ", ";
                        }
                    }
                    enumerationOfAddedAssumptions = enumerationOfAddedAssumptions.substring(0, enumerationOfAddedAssumptions.length()-2); //Remove the last ", "

                    textVersion += String.format(rewritingBundle.getString("inversion")+"\n", inversionLemmaDefinition, enumerationOfAddedAssumptions);
                    break;
                case LEMMA:
                    textVersion += input.toString() + "\n";
                    break;
                case OMEGA:
                    textVersion += indentation;
                    textVersion += rewritingBundle.getString("omega")+"\n";
                    break;
                case PROOF:
                    textVersion += input.toString() + "\n";
                    break;
                case REFLEXIVITY:
                    textVersion += indentation;
                    textVersion += rewritingBundle.getString("reflexivity")+"\n";
                    break;
                case SIMPL: //TODO "simpl in ..."
                    textVersion += indentation;
                    textVersion += String.format(rewritingBundle.getString("simpl")+"\n", previousOutput.getGoal().toString(), output.getGoal().toString());
                    break;
                case SPLIT:
                    break;
                case UNFOLD:
                    textVersion += indentation;
                    String unfoldedDefinition = input.toString().split(" ")[1].replace(".", ""); //Obtains the "A" in "unfold A."
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
            int indentationLevel = input.toString().split(" ")[0].length(); //The bullet length determines the indendation level (e.g., - = 1, -- = 2, --- = 3)
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
        for(InputOutput p : _inputsOutputs) {
            if (p.getInput().toString().equals("Qed.")) { break; }
            if (i == 0) {
                s.push(i);
            }
            else if (i > 0) {
                Integer previousNode = s.pop();

                InputOutput previousPair = _inputsOutputs.get(i-1);
                int numberOfSubgoalsBeforeTactic = previousPair.getOutput().getNumberOfRemainingSubgoals();
                int numberOfSubgoalsAfterTactic = p.getOutput().getNumberOfRemainingSubgoals();

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
            _inputsOutputs.add(index+numberOfInputsInserted, new InputOutput(new Input(bulletsToAddAfter.get(index)), _inputsOutputs.get(index+numberOfInputsInserted-1).getOutput()));
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
        for(InputOutput p : _inputsOutputs) {
            if (p.getInput().toString().equals("Qed.")) { break; }
            if (i == 0) {
                s.push(i);
            }
            else if (i > 0) {
                Integer previousNode = s.pop();

                InputOutput previousPair = _inputsOutputs.get(i-1);
                int numberOfSubgoalsBeforeTactic = previousPair.getOutput().getNumberOfRemainingSubgoals();
                int numberOfSubgoalsAfterTactic = p.getOutput().getNumberOfRemainingSubgoals();

                int addedSubgoals = numberOfSubgoalsAfterTactic - numberOfSubgoalsBeforeTactic;
                if (addedSubgoals > 0) {
                    for(int j=0; j<=addedSubgoals; j++) {
                        s.push(i);
                    }
                    System.out.println(String.format("\"%d. %s\" -> \"%d. %s\";", previousNode, _inputsOutputs.get(previousNode).getInput().toString(), i, _inputsOutputs.get(i).getInput().toString()));
                    bulletStr += "-";
                    bulletLevel.put(i, bulletStr);
                }
                else if (addedSubgoals == 0) {
                    if (bulletLevel.get(previousNode) != null) {
                        bulletsToAddAfter.put(i, bulletLevel.get(previousNode));
                    }
                    System.out.println(String.format("\"%d. %s\" -> \"%d. %s\";", previousNode, _inputsOutputs.get(previousNode).getInput().toString(), i, _inputsOutputs.get(i).getInput().toString()));
                    s.push(i);
                }
                else if (addedSubgoals < 0) {
                    if (bulletLevel.get(previousNode) != null) {
                        bulletsToAddAfter.put(i, bulletLevel.get(previousNode));
                    }
                    System.out.println(String.format("\"%d. %s\" -> \"%d. %s\";", previousNode, _inputsOutputs.get(previousNode).getInput().toString(), i, _inputsOutputs.get(i).getInput().toString()));
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
            coqtop.stop();
        }
    }
}
