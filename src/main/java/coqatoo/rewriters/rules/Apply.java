package coqatoo.rewriters.rules;

import coqatoo.coq.Assumption;
import coqatoo.coq.Input;
import coqatoo.coq.Output;

import java.util.Arrays;
import java.util.ResourceBundle;
import java.util.Set;

public class Apply {
    public static String apply(ResourceBundle bundle, Input input, Output output, Set<coqatoo.coq.Assumption> before, Set<Assumption> after, Output previousOutput) {
        String lemmaName = input.toString().split(" ")[1].replace(".", ""); //Obtains the "A" in "apply A."
        String lemmaDefinition = "  ";
        for (Assumption a : before) {
            if (a.getName().equals(lemmaName)) {
                lemmaDefinition = a.getType();
            }
        }
        //TODO Adapt output if definition is not of the form "A -> B"
        int indexOfLastImplication = lemmaDefinition.lastIndexOf("->");
        if (indexOfLastImplication != -1) {
            String[] propositionsLeftToProve = lemmaDefinition.substring(0, indexOfLastImplication).split("->");
            Arrays.stream(propositionsLeftToProve).map(String::trim).toArray(unused -> propositionsLeftToProve); //Removes whitespace from all elements of the array
            String commaSeparatedPropositionsLeftToProve = String.join(", ", propositionsLeftToProve);
            return String.format(bundle.getString("apply"), lemmaDefinition, previousOutput.getGoal().toString(), commaSeparatedPropositionsLeftToProve);
        }

        return "";
    }
}
