package coqatoo.coq;

import coqatoo.Main;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

import static java.lang.Thread.sleep;

public class Coqtop {

    Boolean _debugging = Main.debug;
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

    public List<InputOutput> execute(String script) {
        String[] scriptLines = script.split("\n");
        List<InputOutput> inputsOutputs = new ArrayList<>();

        try {
            for (String input : scriptLines) {
                _writer.write(input.replaceAll("auto\\.", "info_auto\\.")+"\n"); //FIXME Temporary measure to translate auto to info_auto and obtain the sequence of tactics used on the first execution of Coqtop
                _writer.flush();

                String output = "";
                while (!_reader.ready()) {
                    sleep(1);
                }

                while (_reader.ready()) {
                    output += _reader.readLine() + "\n";
                }

                inputsOutputs.add(new InputOutput(new Input(input), new Output(output)));

                if (_debugging) {
                    System.out.println("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
                    System.out.println("Input: " + input.trim());
                    System.out.println("Output: \n" + output);
                    System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
                }

            }
        }
        catch (Exception e) { e.printStackTrace(); }

        return inputsOutputs;
    }


    public void stop() {
        if (_process.isAlive()) {
            _process.destroy();
        }
    }


}
