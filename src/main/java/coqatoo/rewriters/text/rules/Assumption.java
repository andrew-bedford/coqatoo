package coqatoo.rewriters.text.rules;

import coqatoo.coq.Input;
import coqatoo.coq.Output;

import java.util.ResourceBundle;
import java.util.Set;

public class Assumption {
    public static String apply(ResourceBundle bundle) {
        return bundle.getString("assumption");
    }
}
