Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros.
  intro.
  destruct H as [ H1 | H2 ].
  absurd P.
  assumption.
  apply H0.
  absurd Q.
  assumption.
  apply H0.
Qed.

Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros.
  intro.
  destruct H0 as [ H1 | H2 ].
  absurd P.
  apply H.
  assumption.
  absurd Q.
  apply H.
  assumption.
Qed.

Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  split.
  intro.
  absurd (P \/ Q).
  assumption.
  left.
  assumption.
  intro.
  absurd (P \/ Q).
  assumption.
  right.
  assumption.
Qed.
