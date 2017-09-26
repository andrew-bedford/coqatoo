package coqatoo.coq;

import coqatoo.Main;
import javafx.util.Pair;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

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


}
