Theorem Modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q H1 H2.
  apply H2.
  assumption.
Qed.
