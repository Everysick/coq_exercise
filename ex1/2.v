Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
  intros.
  intro.
  absurd Q.
  destruct H as [ H1 H2 ].
  apply H1.
  destruct H as [ H1 H2 ].
  apply H2 in H0.
  assumption.
Qed.