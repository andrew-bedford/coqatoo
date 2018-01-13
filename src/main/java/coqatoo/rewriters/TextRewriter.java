package coqatoo.rewriters;

import coqatoo.Main;
import coqatoo.coq.*;
import coqatoo.rewriters.Rewriter;
import coqatoo.rewriters.rules.Apply;
import coqatoo.rewriters.rules.Destruct;

import java.util.*;

public class TextRewriter implements Rewriter {

    protected ResourceBundle _rewritingBundle = ResourceBundle.getBundle("RewritingBundle", Main.locale);
    protected String _script;
    protected String _scriptWithUnfoldedAutos;
    protected List<InputOutput> _inputsOutputs;

    protected String generateScriptWithUnfoldedAutos(List<InputOutput> inputsOutputs) {
        String scriptWithUnfoldedAutos = "";
        for(InputOutput p : _inputsOutputs) {
            Input i = p.getInput();
            Output o = p.getOutput();
            if (i.getType() == InputType.AUTO) {
                String[] tacticsUsedByAuto = o.getValue().split("\n");
                for (String s : tacticsUsedByAuto) {
                    if (!s.contains("(* info auto: *)") && !s.contains("No more subgoals")) { //Ignore the first line of the info_auto
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
                    textVersion += indentation;
                    textVersion += Apply.apply(_rewritingBundle, input, output, assumptionsBeforeTactic, assumptionsAddedAfterTactic, previousOutput) + "\n";
                    break;
                case ASSUMPTION:
                    textVersion += indentation;
                    textVersion += coqatoo.rewriters.rules.Assumption.apply(_rewritingBundle) +"\n";
                    break;
                case BULLET:
                    indentation = updatedIndentationLevel(input);
                    textVersion += indentation;
                    textVersion += String.format(_rewritingBundle.getString("bullet")+"\n", input.toString(), output.getGoal().toString());
                    indentation += "  ";
                    break;
                case DESTRUCT:
                    textVersion += indentation;
                    textVersion += Destruct.apply(_rewritingBundle, input)+"\n";
                    break;
                case INTRO:
                case INTROS:
                    textVersion += indentation;
                    textVersion += coqatoo.rewriters.rules.Intros.apply(_rewritingBundle, input, output, assumptionsBeforeTactic, assumptionsAddedAfterTactic, previousOutput) + "\n";

                    break;
                case LEMMA:
                    textVersion += input.toString() + "\n";
                    break;
                case OMEGA:
                    textVersion += indentation;
                    textVersion += _rewritingBundle.getString("omega")+"\n";
                    break;
                case PROOF:
                    textVersion += input.toString() + "\n";
                    break;
                case REFLEXIVITY:
                    textVersion += indentation;
                    textVersion += _rewritingBundle.getString("reflexivity")+"\n";
                    break;
                case SIMPL: //TODO "simpl in ..."
                    textVersion += indentation;
                    textVersion += String.format(_rewritingBundle.getString("simpl")+"\n", previousOutput.getGoal().toString(), output.getGoal().toString());
                    break;
                case SPLIT:
                    break;
                case UNFOLD:
                    textVersion += indentation;
                    String unfoldedDefinition = input.toString().split(" ")[1].replace(".", ""); //Obtains the "A" in "unfold A."
                    textVersion += String.format(_rewritingBundle.getString("unfold")+"\n", unfoldedDefinition, output.getGoal().toString());
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

    protected String updatedIndentationLevel(Input input) {
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
       extractInformation(proofScript);
       String textVersion = getTextVersion();
       textVersion = textVersion.replace("<[{","");
       textVersion = textVersion.replace("}]>","");
       System.out.println(textVersion);
    }

    protected String formatScript(String proofScript) {
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

    protected void extractInformation(String proofScript) {
        _script = proofScript;
        if (_inputsOutputs == null) {
            _inputsOutputs = Main.coqtop.execute(_script);
        }

        _scriptWithUnfoldedAutos = generateScriptWithUnfoldedAutos(_inputsOutputs);
        if (!_scriptWithUnfoldedAutos.equals(_script)) {
            Coqtop coqtop = new Coqtop();
            _inputsOutputs = coqtop.execute(_scriptWithUnfoldedAutos);
            coqtop.stop();
        }
    }
}
