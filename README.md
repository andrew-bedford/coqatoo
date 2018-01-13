# Coqatoo
Due to their numerous advantages, formal proofs and proof assistants, such as Coq, are becoming increasingly popular. However, one disadvantage of using proof assistants is that the resulting proofs can be sometimes hard to understand (e.g., proof below), particularly for less-experienced users. 
```ML
Lemma conj_imp_equiv : forall P Q R:Prop, ((P /\ Q -> R) <-> (P -> Q -> R)).
Proof.
  intros. split. intros H HP HQ. apply H. apply conj. assumption. assumption. intros H HPQ. inversion HPQ. apply H. assumption. assumption.
Qed.
```

Coqatoo (coq-to) attempts to address this issue by generating natural language versions of Coq proofs. For example, from the previous proof, Coqatoo produces the following output (using the option `--mode coq`):
```ML
Lemma conj_imp_equiv : forall P Q R:Prop, ((P /\ Q -> R) <-> (P -> Q -> R)).
Proof.
  (* Given any P, Q, R : Prop. Let us show that (P /\ Q -> R) <-> (P -> Q -> R) is true. *) intros.
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
    (* By our hypothesis P -> Q -> R, we know that R is true if P and Q is true. *) apply H.
    -- (* Case P: *)
       (* True, because it is one of our assumptions. *) assumption.
    -- (* Case Q: *)
       (* True, because it is one of our assumptions. *) assumption.
Qed.
```

It can also generate a tree representation of the proof's structure (using the option `--mode dot`).
<img src="https://i.imgur.com/3vwBaw0.png" width="50%" />

**Note:** Coqatoo is only a proof-of-concept for the moment. There remains much to be done before it can be of real use. 

## Usage
```
--debug                                        Display debugging information
--input [.v file]                              File containing the Coq proof
--language [en (default) | fr]                 Target language
--mode [text (default) | coq | latex | dot]    Output mode
```

## Assumptions
For the moment, Coqatoo makes a few assumptions about the proof:
 - The .v file given as input contains only the proof that we want to convert.
 - Proofs do not use automation (e.g., inline Ltac or the ; operator).
 - Coq's bin path is in your environment

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