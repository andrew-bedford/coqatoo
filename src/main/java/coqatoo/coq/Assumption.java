package coqatoo.coq;

public class Assumption {
    private String _name;
    private String _type;

    public Assumption(String value) {
        _name = value.split(":")[0].trim(); //TODO Cleaner
        _type = value.split(":")[1].trim();
    }

    public String getType() { return _type; }
    public String getName() { return _name; }

    public Boolean isOfKnownType() {
        if (_type.equals("Prop")) { return true; }
        return false;
    }



    //Note: Overriding equals and hashCode is necessary so that the operations on sets of assumptions work properly (e.g., removeAll, containsAll)
    @Override public boolean equals(Object other) {
        if (other == null) return false;
        if (other == this) return true;
        if (!(other instanceof Assumption))return false;

        Assumption otherAssumption = (Assumption)other;

        if (!this._name.equals(otherAssumption._name)) { return false; }
        if (!this._type.equals(otherAssumption._type)) { return false; }

        return true;
    }
    @Override public int hashCode() {
        return _type.hashCode();
    }

}
