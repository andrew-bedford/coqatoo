package coqatoo.rewriters;

import coqatoo.Main;
import coqatoo.coq.*;
import javafx.util.Pair;

import java.util.HashSet;
import java.util.List;
import java.util.ResourceBundle;
import java.util.Set;

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
                    textVersion += String.format(rewritingBundle.getString("bullet"), input.getValue(), output.getGoal().toString());
                    textVersion += " *)\n";
                    indentation += "  ";
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
                    textVersion += "*) ";
                    textVersion += input.getValue()+"\n";
                    break;
                case LEMMA:
                    textVersion += input.getValue() + "\n";
                    break;
                case PROOF:
                    textVersion += input.getValue() + "\n";
                    break;
                case REFLEXIVITY:
                    textVersion += "(* ";
                    textVersion += rewritingBundle.getString("reflexivity");
                    textVersion += "*) ";
                    textVersion += input.getValue()+"\n";
                    break;
                case SPLIT:
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
        _script = proofScript;
        _inputsOutputs = Main.coqtop.execute(_script);

        _scriptWithUnfoldedAutos = generateScriptWithUnfoldedAutos(_inputsOutputs);
        if (!_scriptWithUnfoldedAutos.equals(_script)) {
            Coqtop coqtop = new Coqtop();
            _inputsOutputs = coqtop.execute(_scriptWithUnfoldedAutos);
        }

        System.out.println(getTextVersion());
    }
}
