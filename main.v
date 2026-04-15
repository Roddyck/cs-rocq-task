From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Import Nat Peano.

Global Hint Resolve ltb_spec0 leb_spec0 eqb_spec : bdestruct.

Ltac bdestr X H :=
  let e := fresh "e" in
   evar (e : Prop);
   assert (H : reflect e X); subst e;
    [ eauto with bdestruct
    | destruct H as [H | H];
       [ | try first [apply nlt_ge in H | apply nle_gt in H]]].

Tactic Notation "bdestruct" constr(X) := let H := fresh in bdestr X H.

Tactic Notation "bdestruct" constr(X) "as" ident(H) := bdestr X H.

Section Search1.

Variable array : nat -> nat.

Fixpoint search1 (n x : nat) : bool :=
  match n with
  | 0 => x =? array 0
  | S k => (x =? array n) || search1 k x
  end.

Theorem search1Spec :
  forall n x, (exists i, i < n /\ array i = x) <-> search1 n x = true.
Admitted.

End Search1.

Section Search2.

Variable array2 : nat -> nat -> nat.

Fixpoint search2 (m n x : nat) : bool :=
  match m with
  | 0 => search1 (array2 0) n x
  | S k => search1 (array2 m) n x || search2 k n x
  end.

Theorem search2Spec :
  forall m n x,
  (exists j k, j < m /\ k < n /\ array2 j k = x) <-> search2 m n x = true.
Admitted.

End Search2.
