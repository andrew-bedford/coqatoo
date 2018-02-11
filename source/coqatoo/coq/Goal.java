package coqatoo.coq;

public class Goal {
    private String _value;

    public Goal(String value) {
        _value = value;
    }

    public String getValue() { return _value; }

    @Override public String toString() {
        return _value;
    }
}
