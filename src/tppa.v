Variables A B C : Prop.

Theorem a : A -> B -> A.

Proof.
  intros.
  assumption.
Qed.

Theorem b : A -> (A -> B) -> B.

Proof.
  intros.
  apply H0.
  assumption.
Qed.

Theorem c : A -> (B -> C) -> (A -> B) -> C.

Proof.
  intros.
  apply H0.
  apply H1.
  assumption.
Qed.