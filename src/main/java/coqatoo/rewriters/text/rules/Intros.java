package coqatoo.rewriters.text.rules;

import coqatoo.coq.Assumption;
import coqatoo.coq.Input;
import coqatoo.coq.Output;
import helpers.SetHelper;

import java.util.*;

public class Intros {
    public static String apply(ResourceBundle bundle, Input input, Output output, Set<coqatoo.coq.Assumption> before, Set<Assumption> after, Output previousOutput) {
        String result = "";
        String variables = "";
        String variableNames = "";
        String variablesTypes = "";
        String hypotheses = "";
        Map<String, Set<String>> typesToVariables = new HashMap<>();

        for (Assumption a : after) {
            // To choose whether the rule intros.given or intros.suppose should be used, we need to determine the type of the current assumption.
            Boolean assumptionTypeIsAlsoVariableName = false;
            for (Assumption b : SetHelper.union(before, after)) {
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
                hypotheses += String.format("%s, ", a.getType());
            }
        }

        for (String type : typesToVariables.keySet()) {
            Set<String> variablesWithSameType = typesToVariables.get(type);
            variables += String.format("%s : %s, ", SetHelper.toString(variablesWithSameType), type);

        }

        if (!variables.isEmpty()) {
            variables = variables.substring(0, variables.length() - 2);
            result += String.format(bundle.getString("intros.given"), variables);
        }
        if (!hypotheses.isEmpty()) {
            hypotheses = hypotheses.substring(0, hypotheses.length() - 2);
            result += String.format(bundle.getString("intros.suppose"), hypotheses);
        }
        result += String.format(bundle.getString("intros.goal"), output.getGoal().toString());
        return result;
    }
}
