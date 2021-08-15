Variable A B C : Prop.

Theorem syll : (A -> B) -> (B -> C) -> A -> C. 
Proof.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

Axiom classic : forall P : Prop, (P \/ ~P).

Theorem doubleng : ~~A -> A.
Proof.
  intro.
  elim (classic A).
  intro. assumption.
  intro.
  contradict H.
  assumption.
Qed.

Theorem ex4: forall A : Prop, A -> ~ ~ A.
Proof.
  intro.
  intro.
  contradict H.
  assumption.
Qed.

Theorem ex7: forall (a b : Type) (p : Type -> Prop), p a \/ p b -> exists x : Type, p x.
Proof.
  intro.
  intro.
  intro.
  intro.
  elim H.
  intro.
  exists a. assumption.
  intro.
  exists b. assumption.
Qed.

Theorem ex3: forall A B C D: Prop, (A -> C) /\ (B -> D) -> A /\ B -> C /\ D.
Proof.
  intros.
  elim H.
  elim H0.
  intros.
  split.
  apply H3.
  exact H1.
  apply H4.
  exact H2.
Qed.

Theorem ex8: forall (A : Set) (R : A -> A -> Prop),
    (forall x y z : A, R x y /\ R y z -> R x z) ->
    (forall x y : A, R x y -> R y x) -> forall x : A, (exists y : A, R x y) -> R x x.
Proof.
  intros.
  elim H1. intros.
  apply H0.
  apply H with x0.  
  split.
  exact H2.
  apply H0.      
  exact H2.  
Qed.

Print ex8.


