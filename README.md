# Coqatoo
Coqatoo (coq-to) is a command-line utility that generates natural language versions of Coq proofs.

For example, from the following lemma:
```ML
Lemma conj_imp_equiv : forall P Q R:Prop, ((P /\ Q -> R) <-> (P -> Q -> R)).
Proof.
  intros.
  split.
  -
    intros H HP HQ.
    apply H.
    apply conj.
    --
        assumption.
    --
        assumption.
  -
    intros H HPQ.
    inversion HPQ.
    apply H.
    --
        assumption.
    --
        assumption.
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

Coqatoo was primarily designed for educational purposes. That is, to help Coq newcomers better understand Coq proofs and how they relate to classical proofs.

## Usage
```
-file [.v file]         The file containing the Coq proof.
-language [fr | en]     The target language.
```

## Assumptions
For the moment, Coqatoo makes a few assumptions about the proof:
 - The .v file given as input contains only the proof that we want to convert.
 - Proofs do not use automation (e.g., auto/eauto or the ; operator).
 - Proofs are structured using bullets.

### Supported Tactics
 - apply
 - assumption
 - auto
 - intro
 - intros
 - inversion
 - reflexivity
 - split