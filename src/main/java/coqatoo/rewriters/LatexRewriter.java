package coqatoo.rewriters;

public class LatexRewriter extends TextRewriter {
    public String getTextVersion() {
        String latexVersion = super.getTextVersion();
        latexVersion = latexVersion.replace("<[{", "$");
        latexVersion = latexVersion.replace("}]>", "$");
        latexVersion = latexVersion.replace("Lemma", "\\begin{lemma}");
        latexVersion = latexVersion.replace("Proof.", "\\end{lemma}\\begin{proof}");
        latexVersion = latexVersion.replace("Qed", "\\end{proof}");
        latexVersion = latexVersion.replace("and", "~and~");
        latexVersion = latexVersion.replace("/\\", "\\land");
        latexVersion = latexVersion.replace("<->", "\\Leftrightarrow");
        latexVersion = latexVersion.replace("->", "\\Rightarrow");
        latexVersion = latexVersion.replace("<-", "\\Leftarrow");
        latexVersion = latexVersion.replace("forall", "\\forall");
        latexVersion = latexVersion.replace("\n", "\\\\\n");
        latexVersion = latexVersion.replace("  ", "\\hspace{5mm}");
        latexVersion = latexVersion.replace("\\hspace{5mm}\\\\", "\\\\");
        latexVersion = latexVersion.replace("\\hspace{5mm}\\\\", "\\\\");




        return latexVersion;
    }
}
