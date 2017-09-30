# Coqatoo
Coqatoo (coq-to) is a command-line utility that converts Coq proofs to human-friendly formats.

For example, from the following lemma:
```ML
Lemma conj_imp_equiv : forall P Q R:Prop, ((P /\ Q -> R) <-> (P -> Q -> R)).
Proof.
  intros.
  split.
  - (* -> *)
    intros H HP HQ.
    apply H.
    apply conj; assumption.
  - (* <- *)
    intros H HPQ.
    inversion HPQ.
    apply H; assumption.
Qed.
```
Coqatoo produces the following output:
```
Assume that P, Q and R are arbitrary propositions. [intros]
Let us show that ((P /\ Q) -> R) <-> (P -> Q -> R) is true.
Case ->:
	Suppose that (P /\ Q) -> R, P and Q are true. [intros H HP HQ]
	Let us show that R is true. 
	By our hypothesis (P /\ Q) -> R, we know R is true if (P /\ Q) is true. [apply H]
	[apply conj]
	Case P:
		True, because it is one of our assumptions. [assumption]
	Case Q:
		True, because it is one of our assumptions. [assumption]
	
Case <-:
	Suppose that (P -> Q -> R) and (P /\ Q). [intros H HPQ]
	Let us show that R is true.
	By inversion on (P /\ Q), we know that P and Q are also true. [inversion HPQ]
	By our hypothesis (P -> Q -> R), we know R is true if P and Q are true. [apply H]
	Case P:
		True, because it is one of our assumptions. [assumption]
	Case Q:
		True, because it is one of our assumptions. [assumption]
Qed
```

While Coqatoo was primarily designed for educational purposes (i.e., to help Coq newcomers better understand Coq proofs and how they relate to classical proofs), it can also be used by seasoned veterans of Coq.

## Assumptions
For the moment, Coqatoo makes a few assumptions about the proof:
 - Proofs do not use automation (e.g., auto/eauto or the ; operator).
 - Proofs are structured using bullets.
 - Proofs only use the following tactics: apply, assumption, intro, intros, inversion, split.
 - The .v file given as input contains only the proof that we want to convert.

## Usage
```
-text [.v file] [lemma/theorem name]		 Converts the Coq proof of [lemma/theorem name] in file [file] to plain text.
```