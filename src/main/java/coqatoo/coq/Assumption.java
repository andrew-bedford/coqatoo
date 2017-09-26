package coqatoo.coq;

public class Assumption {
    private String _name;
    private String _value;

    public Assumption(String value) {
        _value = value;
    }

    public String getValue() { return _value; }
    public String getName() { return _name; }

}
