Lemma conj_imp_equiv : forall P Q R:Prop, ((P /\ Q -> R) <-> (P -> Q -> R)).
Proof.
  intros.
  split.
    intros H HP HQ.
    apply H.
    apply conj.
        assumption.
        assumption.
    intros H HPQ.
    inversion HPQ.
    apply H.
        assumption.
        assumption.
Qed.