package coqatoo.coq;

import javafx.util.Pair;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

import static java.lang.Thread.sleep;

public class Coqtop {

    Boolean _debugging = true;
    java.lang.Process _process;
    OutputStream _stdin;
    InputStream _stdout;
    InputStream _stderr;
    BufferedReader _reader;
    BufferedWriter _writer;

    public Coqtop() {
        try {
            ProcessBuilder processBuilder = new ProcessBuilder("coqtop");
            _process = processBuilder.start();
            _stdin = _process.getOutputStream();
            _stdout = _process.getInputStream();
            _stderr = _process.getErrorStream(); //TODO Output coqtop errors
            _reader = new BufferedReader(new InputStreamReader(_stdout));
            _writer = new BufferedWriter(new OutputStreamWriter(_stdin));
            _reader.readLine(); //Ignore the first output of coqtop
        }
        catch (Exception e) { e.printStackTrace(); }
    }

    public List<Pair<Input, Output>> execute(String script) {
        String[] scriptLines = script.split("\n");
        List<Pair<Input, Output>> inputsOutputs = new ArrayList<>();

        try {
            for (String input : scriptLines) {
                _writer.write(input+"\n");
                _writer.flush();

                String output = "";
                while (!_reader.ready()) {
                    sleep(1);
                }

                while (_reader.ready()) {
                    output += _reader.readLine() + "\n";

                }
                inputsOutputs.add(new Pair<>(new Input(input), new Output(output)));

                if (_debugging) {
                    System.out.println(input);
                    System.out.println(output);
                }

            }
        }
        catch (Exception e) { e.printStackTrace(); }

        return inputsOutputs;
    }


}
