package coqatoo.coq;

public class InputOutput {
    Input _input;
    Output _output;

    public InputOutput(Input input, Output output) {
        _input = input;
        _output = output;
    }

    public Input getInput() { return _input; }
    public Output getOutput() {return _output; }
}
