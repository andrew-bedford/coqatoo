package coqatoo.coq;

public class Assumption {
    private String _name;
    private String _value;

    public Assumption(String value) { //TODO Other name than "value"?
        _name = value.split(":")[0].trim(); //TODO Cleaner
        _value = value.split(":")[1].trim();
    }

    public String getValue() { return _value; }
    public String getName() { return _name; }

    public Boolean isValueKnownType() {
        if (_value.equals("Prop")) { return true; }
        return false;
    }



    //Note: Overriding equals and hashCode is necessary so that the operations on sets of assumptions work properly (e.g., removeAll, containsAll)
    @Override public boolean equals(Object other) {
        if (other == null) return false;
        if (other == this) return true;
        if (!(other instanceof Assumption))return false;

        Assumption otherAssumption = (Assumption)other;

        if (!this._name.equals(otherAssumption._name)) { return false; }
        if (!this._value.equals(otherAssumption._value)) { return false; }

        return true;
    }
    @Override public int hashCode() {
        return _value.hashCode();
    }

}
