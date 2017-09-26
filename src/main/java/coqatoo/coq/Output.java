package coqatoo.coq;

import java.util.EnumSet;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.CopyOnWriteArraySet;

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
            if (t[1].indexOf("\n") != -1) {
                return new Goal (t[1].split("\n")[0].trim());
            }

            return new Goal(t[1].trim());
        }

        return new Goal("");
    }

    private Set<Assumption> determineAssumptions(String value) {
        Set<Assumption> assumptions = new HashSet<>();

        //Example of "value"
        //1 focused subgoal\n(unfocused: 0)\n \n P, Q, R : Prop\n H : P -> Q -> R\n HPQ : P /\ Q\n H0 : P\n H1 : Q\n ============================\n R\n
        String[] t = value.split("============================\n ");
        if (t.length > 1) {
            t = t[0].split("\n  \n ");
            if (t.length > 1) {
                t = t[1].split("\n "); //Splits "P, Q, R : Prop" from "H : P -> Q -> R" from "HPQ : P /\ Q" from "H0 : P" from "H1 : Q"

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
                            System.out.println("ADDING ASSUMPT " + s + "\n");
                        }

                    }
                }
            }

        }

        return assumptions;
    }
}
