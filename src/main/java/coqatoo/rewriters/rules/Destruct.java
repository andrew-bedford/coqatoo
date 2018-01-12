package coqatoo.rewriters.rules;

import coqatoo.coq.Input;

import java.util.ResourceBundle;

public class Destruct {
    public static String apply(ResourceBundle bundle, Input input) {
        String destructedObject = input.toString().substring(input.toString().indexOf(" "), input.toString().length()-1); //Obtains the "(A B)" in "destruct (A B)."
        return String.format(bundle.getString("destruct"), destructedObject);
    }
}
