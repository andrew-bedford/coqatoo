package coqatoo.coq;

public class Input {
    private String _value;
    private InputType _type;

    public Input(String value) {
        _value = value.trim(); //TODO Remove existing comments from input
        _type = determineType(_value);
    }

    public String getValue() { return _value; }
    public InputType getType() { return _type; }

    private InputType determineType(String value) {
        if (value.startsWith("Abort")) { return InputType.ABORT; }
        if (value.startsWith("apply")) { return InputType.APPLY; }
        if (value.startsWith("assumption")) { return InputType.ASSUMPTION; }
        if (value.startsWith("auto")) { return InputType.AUTO; }
        if (value.startsWith("-") || value.startsWith("+") || value.startsWith("*")) { return InputType.BULLET; } //TODO Add support for { } bullets
        if (value.startsWith("intros")) { return InputType.INTROS; }
        if (value.startsWith("intro")) { return InputType.INTRO; }
        if (value.startsWith("inversion")) { return InputType.INVERSION; }
        if (value.startsWith("Lemma")) { return InputType.LEMMA; }
        if (value.startsWith("DefaultRewriter")) { return InputType.PROOF; }
        if (value.startsWith("split")) { return InputType.SPLIT; }
        if (value.startsWith("Qed")) { return InputType.QED; }

        return InputType.UNKNOWN;
    }
}
