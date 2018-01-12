package coqatoo.rewriters.rules;

import coqatoo.coq.Assumption;
import coqatoo.coq.Input;
import coqatoo.coq.Output;

import java.util.ResourceBundle;
import java.util.Set;

public class Inversion {
    public static String apply(ResourceBundle bundle, Input input, Output output, Set<coqatoo.coq.Assumption> before, Set<Assumption> after) {
        String inversionLemmaName = input.toString().split(" ")[1].replace(".", ""); //Obtains the "A" in "apply A."
        String inversionLemmaDefinition = "";
        for (Assumption a : before) {
            if (a.getName().equals(inversionLemmaName)) {
                inversionLemmaDefinition = a.getType();
            }
        }

        String enumerationOfAddedAssumptions = "";
        for (Assumption a : after) {
            if (!a.typeContainsSpaces()) {
                enumerationOfAddedAssumptions += a.getType() + ", ";
            }
        }
        enumerationOfAddedAssumptions = enumerationOfAddedAssumptions.substring(0, enumerationOfAddedAssumptions.length()-2); //Remove the last ", "

        return String.format(bundle.getString("inversion"), inversionLemmaDefinition, enumerationOfAddedAssumptions);
    }
}
