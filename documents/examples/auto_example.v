Lemma auto_example : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.