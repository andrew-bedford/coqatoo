package coqatoo.coq;

import java.util.HashSet;
import java.util.Set;

public class Output {
    private String _value;
    private Set<Assumption> _assumptions;
    private Goal _goal;

    public Output(String value) {
        _value = value;
        _assumptions = determineAssumptions(_value);
        _goal = determineGoal(_value);
    }

    public String getValue() { return _value; }

    public Set<Assumption> getAssumptions() { return _assumptions; }

    public Goal getGoal() { return _goal; }

    private Goal determineGoal(String value) {
        String[] t = value.split("============================\n ");
        if (t.length > 1) {
            return new Goal(t[1]);
        }

        return new Goal("");
    }

    private Set<Assumption> determineAssumptions(String value) {
        Set<Assumption> assumptions = new HashSet<>();

        String[] t = value.split("============================\n ");
        if (t.length > 1) {
            t = t[0].split("\n  \n ");
            if (t.length > 1) {
                t = t[1].split("\n ");

                for (String s : t) {
                    if (!s.trim().isEmpty()) {

                        //If the assumption has the form "P, Q : Prop", then add two assumptions "P : Prop" and "Q : Prop"
                        String[] namesAndType = s.split(" : ");
                        String type = namesAndType[1];
                        String[] names = namesAndType[0].split(", ");
                        if (names.length > 1) {
                            for (String name : names) {
                                assumptions.add(new Assumption(name + " : " + type));
                            }
                        }
                        else {
                            assumptions.add(new Assumption(s));
                        }

                    }
                }
            }

        }

        return assumptions;
    }
}
