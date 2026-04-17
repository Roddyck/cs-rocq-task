(** * Проект номер 3. Поиск числа в двумерном массиве.

Сначала задача решается для одномерного массива, затем с использованием
полученных результатов для двумерного массива. *)

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

(** Функция [array] моделирует массив, где индексы строго меньше некоторого
параметра [n], т.о. [n] - длина массива *)
Variable array : nat -> nat.

(** для пустого массива ([n = 0]) возвращаем [false]. Для непустого,
если [x] находится в массиве [(array 0, ..., array (n - 1))], то возвращаем [true], иначе [false] *)
Fixpoint search1 (n x : nat) : bool :=
  match n with
  | 0 => false
  | S k => (x =? array k) || search1 k x 
  end.

(** Далее следуют две вспомогательные леммы, доказывающие шаг индукции при доказательстве
 в соответствующий направлениях (-> и <-). *)
Lemma search1Spec_forward_step :
  forall n x,
  ((exists i, i < n /\ array i = x) -> search1 n x = true) ->
  ((exists i, i < S n /\ array i = x) -> search1 (S n) x = true).
Proof.
  intros n x IH.
  intros [i [H1 H2]]. simpl. assert (i < n \/ i = n) by lia.
  destruct H as [Hlt | Heq].
  * bdestruct (x =? array n); [reflexivity |]. simpl. apply IH. exists i. lia.
  * bdestruct (x =? array n); [reflexivity |]. simpl. apply IH. exists i. subst i. lia.
Qed.

Lemma search1Spec_backward_step :
  forall n x,
  (search1 n x = true -> (exists i, i < n /\ array i = x)) ->
  (search1 (S n) x = true -> (exists i, i < S n /\ array i = x)).
Proof.
  intros n x IH.
  intros H. simpl in H. bdestruct (x =? array n).
  * exists n. lia.
  * simpl in H. apply IH in H. destruct H as [i [H1 H2]].
    exists i. split; lia.
Qed.

Theorem search1Spec :
  forall n x, (exists i, i < n /\ array i = x) <-> search1 n x = true.
Proof.
  split.
  * induction n as [| n IH].
    - intros [i [H1 H2]]. lia.

    - apply search1Spec_forward_step. exact IH. 

  * induction n as [| n IH].
    - intros H. simpl in H. discriminate H.

    - apply search1Spec_backward_step. exact IH.
Qed.

End Search1.

Section Search2.

(** [array2] моделирует двумерный массив, где параметры - количество строк и
столбцов соответственно. *)
Variable array2 : nat -> nat -> nat.

(** [m] и [n] - количество строк и столбцов соответственно.
Аналогично одномерному массиву, при [m = 0] массив пуст и возвращаем [false].
В случае непустого массива возвращаем [true], если [x] встречается в массиве,
иначе возвращаем [false]. *)
Fixpoint search2 (m n x : nat) : bool :=
  match m with
  | 0 => false 
  | S k => search1 (array2 k) n x || search2 k n x
  end.

(** Аналогичные [search1Spec] вспомогательные леммы *)
Lemma search2Spec_forward_step :
  forall m n x,
  ((exists j k, j < m /\ k < n /\ array2 j k = x) -> search2 m n x = true) ->
  ((exists j k, j < S m /\ k < n /\ array2 j k = x) -> search2 (S m) n x = true).
Proof.
  intros m n x IH.
  intros [j [k [H1 [H2 H3]]]]. simpl. assert (j < m \/ j = m) by lia.
  destruct H as [Hlt | Heq]. clear H1.

  * destruct (search1 (array2 m) n x) eqn:Hb; [reflexivity |]. simpl. 
    apply IH. exists j, k. lia.

  (** противоречивый случай ([j = m]) и при этом [search1 (array2 m) n x = false]. *)
  * clear H1. destruct (search1 (array2 m) n x) eqn:Hb; [reflexivity |]. simpl.
    (** докажем, что должно быть [search1 (array2 m) n x = true] *)
    assert (search1 (array2 m) n x = true) as Htrue.
    - rewrite <- search1Spec. exists k. subst j. split; assumption.

    - rewrite Hb in Htrue. discriminate Htrue.
Qed.

Lemma search2Spec_backward_step :
  forall m n x,
  (search2 m n x = true -> (exists j k, j < m /\ k < n /\ array2 j k = x)) ->
  (search2 (S m) n x = true -> (exists j k, j < S m /\ k < n /\ array2 j k = x)).
Proof.
  intros m n x IH.
  intros H. simpl in H. destruct (search1 (array2 m) n x) eqn:Hb.

  * rewrite <- search1Spec in Hb. destruct Hb as [k [H1 H2]].
    exists m, k. split; lia.

  * simpl in H. apply IH in H. destruct H as [j [k [H1 [H2 H3]]]].
    exists j, k. lia.
Qed.

Theorem search2Spec :
  forall m n x,
  (exists j k, j < m /\ k < n /\ array2 j k = x) <-> search2 m n x = true.
Proof.
  split.
  * induction m as [| m IH].
    - intros [j [k [H1 [H2 H3]]]]. lia.

    - apply search2Spec_forward_step. exact IH.

  * induction m as [| m IH].
    - intros H. simpl in H. discriminate H.

    - apply search2Spec_backward_step. exact IH.
Qed.

End Search2.
