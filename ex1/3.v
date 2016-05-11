Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros.
  destruct H as [ H1 | H2 ].
  absurd P.
  apply H0.
  apply H1.
  assumption.
Qed.