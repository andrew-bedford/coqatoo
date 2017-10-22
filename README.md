# Coqatoo
Coqatoo (coq-to) is a command-line utility that generates natural language versions of Coq proofs.

For example, from the following poorly-structured lemma:
```ML
Lemma conj_imp_equiv : forall P Q R:Prop, ((P /\ Q -> R) <-> (P -> Q -> R)).
Proof.
  intros. split. intros H HP HQ. apply H. apply conj. assumption. assumption. intros H HPQ. inversion HPQ. apply H. assumption. assumption.
Qed.
```
Coqatoo produces the following output:
```ML
Lemma conj_imp_equiv : forall P Q R:Prop, ((P /\ Q -> R) <-> (P -> Q -> R)).
Proof.
  (* Assume that P, Q and R are arbitrary objects of type Prop. Let us show that (P /\ Q -> R) <-> (P -> Q -> R) is true. *) intros.
  split.
  - (* Case (P /\ Q -> R) -> P -> Q -> R: *)
    (* Suppose that P, Q and P /\ Q -> R are true. Let us show that R is true. *) intros H HP HQ.
    (* By our hypothesis P /\ Q -> R, we know that R is true if P /\ Q  is true. *) apply H.
    apply conj.
    -- (* Case P: *)
       (* True, because it is one of our assumptions. *) assumption.
    -- (* Case Q: *)
     (* True, because it is one of our assumptions. *) assumption.
  - (* Case (P -> Q -> R) -> P /\ Q -> R: *)
    (* Suppose that P /\ Q and P -> Q -> R are true. Let us show that R is true. *) intros H HPQ.
    (* By inversion on P /\ Q, we know that P, Q are also true. *) inversion HPQ.
    (* By our hypothesis P -> Q -> R, we know that R is true if P -> Q  is true. *) apply H.
    -- (* Case P: *)
       (* True, because it is one of our assumptions. *) assumption.
    -- (* Case Q: *)
       (* True, because it is one of our assumptions. *) assumption.
Qed.
```

It can also be used to generate a tree representation of the proof's structure.
![proof tree](https://i.imgur.com/3vwBaw0.png)

Coqatoo was primarily designed for educational purposes. That is, to help Coq newcomers better understand Coq proofs and how they relate to classical proofs.

## Usage
```
--debug                                        Display debugging information
--file [.v file]                               File containing the Coq proof
--language [en (default) | fr]                 Target language
--mode [plain (default) | annotated | dot]     Output mode
```

## Assumptions
For the moment, Coqatoo makes a few assumptions about the proof:
 - The .v file given as input contains only the proof that we want to convert.
 - Proofs do not use automation (e.g., inline Ltac or the ; operator).

### Supported Tactics
 - apply
 - assumption
 - auto
 - destruct
 - intro
 - intros
 - intuition
 - inversion
 - omega
 - reflexivity
 - simpl
 - split
 - unfold