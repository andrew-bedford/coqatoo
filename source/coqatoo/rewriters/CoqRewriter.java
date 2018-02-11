package coqatoo.rewriters;

import coqatoo.coq.*;
import coqatoo.rewriters.rules.Apply;
import coqatoo.rewriters.rules.Inversion;

import java.util.*;

public class CoqRewriter extends TextRewriter {

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
                    textVersion += "(* ";
                    textVersion += Apply.apply(_rewritingBundle, input, output, assumptionsBeforeTactic, assumptionsAddedAfterTactic, previousOutput);
                    textVersion += " *) ";
                    textVersion += input.toString()+"\n";
                    break;
                case ASSUMPTION:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += coqatoo.rewriters.rules.Assumption.apply(_rewritingBundle);
                    textVersion += "*) ";
                    textVersion += input.toString()+"\n";
                    break;
                case BULLET:
                    indentation = updatedIndentationLevel(input);
                    textVersion += indentation;
                    textVersion += input.toString();
                    textVersion += " (* ";
                    textVersion += String.format(_rewritingBundle.getString("bullet"), "", output.getGoal().toString());
                    textVersion += " *)\n";
                    indentation += "  ";
                    break;
                case DESTRUCT:
                    String destructedObject = input.toString().substring(input.toString().indexOf(" "), input.toString().length()-1); //Obtains the "(A B)" in "destruct (A B)."
                    textVersion += "(* ";
                    textVersion += String.format(_rewritingBundle.getString("destruct"), destructedObject);
                    textVersion += "*) ";
                    textVersion += input.toString()+"\n";
                    break;
                case INTRO:
                case INTROS:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += coqatoo.rewriters.rules.Intros.apply(_rewritingBundle, input, output, assumptionsBeforeTactic, assumptionsAddedAfterTactic, previousOutput);
                    textVersion += " *) ";
                    textVersion += input.toString()+"\n";
                    break;
                case INTUITION:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += String.format(_rewritingBundle.getString("intuition"), previousOutput.getGoal().toString());
                    textVersion += " *)";
                    textVersion += input.toString()+"\n";
                    break;
                case INVERSION:
                    textVersion += indentation;

                    textVersion += "(* ";
                    textVersion += Inversion.apply(_rewritingBundle, input, output, assumptionsBeforeTactic, assumptionsAddedAfterTactic);
                    textVersion += " *) ";
                    textVersion += input.toString()+"\n";
                    break;
                case LEMMA:
                    textVersion += input.toString() + "\n";
                    break;
                case OMEGA:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += _rewritingBundle.getString("omega");
                    textVersion += " *)";
                    textVersion += input.toString()+"\n";
                    break;
                case PROOF:
                    textVersion += input.toString() + "\n";
                    break;
                case REFLEXIVITY:
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += _rewritingBundle.getString("reflexivity");
                    textVersion += " *)";
                    textVersion += input.toString()+"\n";
                    break;
                case SIMPL: //TODO "simpl in ..."
                    textVersion += indentation;
                    textVersion += "(* ";
                    textVersion += String.format(_rewritingBundle.getString("simpl"), previousOutput.getGoal().toString(), output.getGoal().toString());
                    textVersion += " *)";
                    textVersion += input.toString()+"\n";
                    break;
                case SPLIT:
                    textVersion += indentation;
                    textVersion += input.toString() + "\n";
                    break;
                case UNFOLD:
                    textVersion += indentation;
                    String unfoldedDefinition = input.toString().split(" ")[1].replace(".", ""); //Obtains the "A" in "unfold A."
                    textVersion += "(* ";
                    textVersion += String.format(_rewritingBundle.getString("unfold"), unfoldedDefinition, output.getGoal().toString());
                    textVersion += " *)";
                    textVersion += input.toString()+"\n";
                    break;
                case QED:
                    textVersion += input.toString() + "\n";
                    break;
                default:
                    textVersion += indentation;
                    textVersion += input.toString() + "\n";
                    break;
            }

            i++;
        }

        textVersion = textVersion.replace("<[{","");
        textVersion = textVersion.replace("}]>","");
        return textVersion;
    }
}
