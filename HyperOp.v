Require Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Arith.PeanoNat.


(** * Definition *)

(** Hyperoperations generalize addition to multiplication
to exponentiation. *)

Fixpoint hyperop (n a b : nat) : nat :=
  let fix hyperop_inner (b_inner : nat) : nat :=
     match n, b_inner with
       | O,    _    => S b
       | 1,    O    => a
       | 2,    O    => 0
       | _,    O    => 1
       | S n', S b' => hyperop n' a (hyperop_inner b')
     end
  in hyperop_inner b.

Notation "a [ n ] b" := (hyperop n a b)
  (at level 50, left associativity).


(** * General Background *)

(** The following are useful throughout the file.
I define them here so as not to break up the flow of
the document later on. *)

(** ** Lemmas *)

Lemma leq_0_nat:
  forall (n:nat), 0 <= n.
Proof.
  intros n. omega.
Qed.


Lemma pow_1_n:
  forall (n : nat), 1 ^ n = 1.
Proof.
  intros n. induction n as [| n' IH].
  - apply Nat.pow_0_r.
  - rewrite Nat.pow_succ_r.
    + rewrite IH. reflexivity.
    + apply leq_0_nat.
Qed.


Theorem gt_to_exists_1:
  forall (x : nat), x > 0 <-> exists j, x = S j.
Proof.
  intros x. split.
  - intros x_gt_0.
    destruct x as [| x' ].
    + cut (~ (0 > 0)).
      * intros contra. contradiction.
      * omega.
    + exists x'. reflexivity.
  - intros exists_j.
    destruct exists_j.
    destruct x0. (*as [| x0' IH ].*)
    + rewrite H; auto.
    + rewrite H; omega.
Qed.

Theorem gt_to_exists_2:
  forall (x : nat), x > 1 <-> exists j, x = S (S j).
Proof.
  intros x. split.
  - intros x_gt_1.
    destruct x as [| x' ].
    + cut (~ (0 > 1)).
      * intros contra. contradiction.
      * omega.
    + destruct x' as [| x'' ].
      * cut (~ (1 > 1)).
        intros contra. contradiction.
        { omega. }
      * exists x''. reflexivity.
  - intros exists_j. destruct exists_j.
    destruct x0.
    + rewrite H; auto.
    + rewrite H; omega.
Qed.

Lemma gt_to_exists:
  forall (x y : nat), x > (y+1) -> exists j, x = S (S j).
Proof.
  intros x y H.
  assert (O_Sn: forall n, n + 1 = S n). { intros; omega. }
  rewrite O_Sn in H.
  induction y as [| y' IH_y ].
  - apply gt_to_exists_2. assumption.
  - apply IH_y. omega.
Qed.



(** ** Tactics *)

(** Handle [n] in four cases:
  [n = 0, 1, 2, 3+]
*)

(* Helper tactic for destruct_hyp *)
Ltac destruct_hyp_ lvl n :=
  match lvl with
    | 0 => destruct n as [| n'' ]; try destruct_hyp_ 1 n''
    | 1 => destruct n as [| n'  ]; try destruct_hyp_ 2 n'
    | _ => destruct n
   end.

(* Analyze n in cases: n = 0, 1, 2, 3+ *)
Ltac destruct_hyp n := destruct_hyp_ 0 n.



(** Given [n > 0], introduce a variable [a] such that
[n = S a], along with a proof [b] of this fact. *)

Ltac make_pred_1 H a b :=
  apply gt_to_exists_1 in H as H';
  destruct H' as [a b].

Tactic Notation
  "make_pred_1" ident(H) "as" "[" ident(a) ident(b) "]" :=
  make_pred_1 H a b.


(** Given [n > 1], introduce a variable [a] such that
[n = S (S a)], along with a proof [b] of this fact. *)

Ltac make_pred_2 H a b :=
  apply gt_to_exists_2 in H as H';
  destruct H' as [a b].

Tactic Notation
  "make_pred_2" ident(H) "as" "[" ident(a) ident(b) "]" :=
  make_pred_2 H a b.



(** * Basics *)

(** ** Base Cases *)

(** The following are the base cases for hyperoperation;
  namely, when [n = 0] or [b = 0]. *)


(* Base case: n = 0 *)
Theorem hyp0_successor:
  forall (a b : nat), a [0] b = S b.
Proof.
  intros a b. destruct b; reflexivity.
Qed.

(* Base case: n = 1, b = 0 *)
Theorem base_1_0:
  forall (a : nat), a [1] 0 = a.
Proof.
  intros a. simpl. reflexivity.
Qed.

(* Base case: n = 2, b = 0 *)
Theorem base_2_0:
  forall (a : nat), a [2] 0 = 0.
Proof.
  intros a. simpl. reflexivity.
Qed.

(* Base case: n >= 3, b = 0 *)
Theorem base_3p_0:
  forall (n a : nat), a [S (S (S n))] 0 = 1.
Proof.
  intros n a. simpl. reflexivity.
Qed.


(** ** Recursive Step *)

(** Expand the recursive part of the definition:
  [a [n+1] b+1 = a n (a [n+1] b)
*)

(* Recursive step: a [n+1] b+1 = a n (a [n+1] b) *)
Theorem expand_Sn_Sb:
  forall (n a b : nat),
  a [S n] S b = a [n] (a [S n] b).
Proof.
  intros n a b.
  induction n as [| n' H].
  - reflexivity.
  - induction b as [| b' Hb].
    + induction n' as [| n'' Hn''].
      * simpl. reflexivity.
      * rewrite base_3p_0.
        simpl. reflexivity.
    + induction n' as [| n'' Hn''].
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.


(** ** Equivalence with basic operations *)

(** Hyper-operations generalize the relationship between
addition, multiplication, and exponentiation. Specifically:

- If [n = 1], the hyper-operation is equivalent to addition.
- If [n = 2], the hyper-operation is equivalent to multiplication.
- If [n = 3], the hyper-operation is equivalent to exponentiation.

*)

(* If n = 1, equivalent to addition *)
Theorem hyp1_addition:
  forall a b, a [1] b = a + b.
Proof.
  intros a.
  induction b as [| b' IH].
  - unfold hyperop. auto.
  - rewrite (expand_Sn_Sb 0 a b').
    rewrite IH.
    rewrite hyp0_successor.
    auto.
Qed.

(* If n = 2, equivalent to multiplication *)
Theorem hyp2_multiplication:
  forall a b, a [2] b = a * b.
Proof.
  intros a b.
  induction b as [| b' IH].
  - simpl. omega.
  - rewrite <- mult_n_Sm.
    rewrite expand_Sn_Sb. rewrite hyp1_addition.
    rewrite IH. omega.
Qed.

(* If n = 3, equivalent to exponentiation *)
Theorem hyp3_exponentiation:
  forall a b, a [3] b = a ^ b.
Proof.
  intros a b.
  induction b as [| b' IH].
  - rewrite base_3p_0. rewrite Nat.pow_0_r. reflexivity.
  - rewrite expand_Sn_Sb. rewrite IH.
    rewrite hyp2_multiplication.
    rewrite Nat.pow_succ_r.
    + reflexivity.
    + apply leq_0_nat.
Qed.

(** For [n = 4], some sources use the term "tetration".
Above that point, though, the operations aren't really
individually named. *)

Notation "a ^^ b" := (hyperop 4 a b)
  (at level 50, left associativity).

Theorem hyp4_tetration:
  forall a b, a [4] b = a ^^ b.
Proof.
  auto.
Qed.





(** * Chapter 2: Some Basic Equalities *)

(** *** Lemma 2.1
Suppose [n > 1]. Then [a[n]1 = a].
*)

Lemma b1_refl:
  forall (a n : nat), a [S (S n)] 1 = a.
Proof.
  intros a n.
  induction n as [| n' IH ].
  - intros; simpl; reflexivity.
  - rewrite expand_Sn_Sb. apply IH.
Qed.


Theorem b1_n_m:
  forall (n m a : nat), a [S (S n)] 1 = a [S (S m)] 1.
Proof.
  intros n m a.
  repeat rewrite b1_refl. reflexivity.
Qed.


(** *** Lemma 2.2
Suppose [n > 2]. Then [1[n]b = 1].
 *)

Lemma a1_eq_1:
  forall (n b : nat), 1 [S (S (S n))] b = 1.
Proof.
  intros n.
  induction n as [| n' IH ].
  - intros b. rewrite hyp3_exponentiation.
    apply pow_1_n.
  - destruct b.
    + apply base_3p_0.
    + rewrite expand_Sn_Sb.
      rewrite IH.
      reflexivity.
Qed.






(** * Chapter 3: Some Basic Inequalities *)

(** *** Lemma 3.1
  Suppose c > b > a. Then c > a + 1.
 *)

Lemma no_nats_between:
  forall (a b c : nat), c > b -> b > a -> c > a+1.
Proof.
  intros; omega.
Qed.

Lemma gt_implies_ge:
  forall (a b : nat), a > b -> a >= S b.
Proof.
  intros; omega.
Qed.

Lemma gt_trans_ge:
  forall (a b c : nat), c > b -> b > a -> c >= a+1.
Proof.
  intros; omega.
Qed.

Lemma gt_plus1_S_r:
  forall (x y : nat), x > y+1 <-> x > S y.
Proof.
  intros; omega.
Qed.









(** ** Section 3.1: A hyper-product is larger than its operands.
 *)



(** *** Lemma 3.2:
Suppose a > 1, b > 1, n > 0. Then a[n]b > a.
 *)

Lemma hyp_gt_a:
  forall (n a b : nat), (S (S a)) [S n] (S (S b)) > (S (S a)).
Proof.
  intros n.
  induction n as [| n' IH_n].
  - intros a b. rewrite hyp1_addition. omega.
  - intros a. induction b as [| b' IH_b].
    + rewrite expand_Sn_Sb.
      rewrite b1_refl.
      apply IH_n.
    + rewrite expand_Sn_Sb.
      apply (no_nats_between 0) in IH_b.
      apply gt_to_exists in IH_b. destruct IH_b as [x x_eq].
      rewrite x_eq. apply IH_n.
      omega.
Qed.



(* Lemma 3.2:
Suppose a > 1, b > 1, n > 0. Then a[n]b > a.
 *)
Lemma hyp_gt_a_alt:
  forall (n a b : nat), (n > 0) -> (a > 1) -> (b > 1) ->
  a [n] b > a.
Proof.
  intros n.
  induction n as [| n' IH_n ].
  - intros a b. omega.
  - intros a b. intros Sn_gt_0 a_gt_1 b_gt_1.
    make_pred_2 a_gt_1 as [a0 H_a].
    make_pred_2 b_gt_1 as [b0 H_b].
    rewrite H_a. rewrite H_b. apply hyp_gt_a.
Qed.














