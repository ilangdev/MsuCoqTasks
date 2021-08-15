Theorem ex3: forall A B C D: Prop, (A -> C) /\ (B -> D) -> A /\ B -> C /\ D.
Proof.
  intros.
  split.
  elim H. intros.
  elim H0. intros.
  apply H1.
  exact H3.
  elim H. intros.
  elim H0. intros.
  apply H2.
  assumption.
Qed.

Axiom classic: forall P : Prop, P \/ ~P.

Theorem doubleng: forall A : Prop, A -> ~~A. 
Proof.
  intro.
  elim (classic A).
  intros.
  contradict H.
  assumption.
  intros.
  contradict H0.
  assumption.
Qed.

Theorem ex4: forall A : Prop, A -> ~~A.
Proof.
  intros.
  contradict H.
  assumption.
Qed.

Theorem ex8: forall (A : Set) (R : A -> A -> Prop),
             (forall x y z : A, R x y /\ R y z -> R x z) ->
             (forall x y : A, R x y -> R y x) ->
             forall x : A, (exists y : A, R x y) -> R x x.
Proof.
  intros.
  elim H1. intros.
  apply H with x0.
  split.
  assumption.
  exact (H0 x x0 H2).
Qed.


