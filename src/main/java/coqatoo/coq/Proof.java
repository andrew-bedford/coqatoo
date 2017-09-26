package coqatoo.coq;

import coqatoo.Main;
import javafx.util.Pair;

import java.io.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static java.lang.Thread.sleep;

public class Proof {
    String _script;
    List<Pair<Input, Output>> _inputsOutputs;

    public Proof(String script) {
        _script = script;
        _inputsOutputs = Main.coqtop.execute(_script);
    }

    public Goal getProofGoal() {
        for(Pair<Input, Output> p : _inputsOutputs) {
            Input i = p.getKey();
            Output o = p.getValue();
            if (i.getType() == InputType.LEMMA) {
                return o.getGoal();
            }
        }

        return null;
    }

    //TODO Insert rewrite logic here
    public String getTextVersion() {
        String textVersion = "";

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
                    String lemmaDefinition = "";
                    for (Assumption a : assumptionsBeforeTactic) {
                        if (a.getName().equals(lemmaName)) {
                            lemmaDefinition = a.getValue();
                        }
                    }
                    //TODO Adapt output if definition is not of the form "A -> B"
                    int indexOfLastImplication = lemmaDefinition.lastIndexOf("->");
                    if (indexOfLastImplication != -1) {
                        textVersion += String.format("By our hypothesis %s, we know that %s is true if %s is true.\n", lemmaDefinition, previousOutput.getGoal().toString(), lemmaDefinition.substring(0, indexOfLastImplication));
                    }
                    break;
                case ASSUMPTION:
                    textVersion += "True, because it is one of our assumptions.\n";
                    break;
                case BULLET:
                    textVersion += String.format(" - Case %s:\n", output.getGoal().toString());
                    break;
                case INTROS:
                    for (Assumption a : assumptionsAddedAfterTactic) {
                        if (a.isValueKnownType()) {
                            textVersion += String.format("Assume that %s is an arbitrary object of type %s. ", a.getName(), a.getValue());
                        }
                        else {
                            textVersion += String.format("Suppose that %s is true. ", a.getValue());
                        }
                    }

                    textVersion += String.format("Let us show that %s is true.\n", output.getGoal().toString());
                    break;
                case INVERSION:
                    String inversionLemmaName = input.getValue().split(" ")[1].replace(".", ""); //Obtains the "A" in "apply A."
                    String inversionLemmaDefinition = "";
                    for (Assumption a : assumptionsBeforeTactic) {
                        if (a.getName().equals(inversionLemmaName)) {
                            inversionLemmaDefinition = a.getValue();
                        }
                    }

                    String enumerationOfAddedAssumptions = "";
                    for (Assumption a : assumptionsAddedAfterTactic) {
                        if (!a.isValueKnownType()) {
                            enumerationOfAddedAssumptions += a.getValue() + ", ";
                        }
                    }
                    enumerationOfAddedAssumptions = enumerationOfAddedAssumptions.substring(0, enumerationOfAddedAssumptions.length()-2); //Remove the last ", "

                    textVersion += String.format("By inversion on %s, we know that %s are also true.\n", inversionLemmaDefinition, enumerationOfAddedAssumptions);
                    break;
                case LEMMA:
                    textVersion += input.getValue() + "\n";
                    break;
                case PROOF:
                    textVersion += input.getValue() + "\n";
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


}
