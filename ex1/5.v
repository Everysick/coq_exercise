Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
Proof.
  intros.
  intro.
  absurd (P \/ ~ P).
  assumption.
  right.
  intro.
  absurd (P \/ ~ P).
  assumption.
  left.
  assumption.
Qed.
