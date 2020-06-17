Require Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Arith.PeanoNat.


Fixpoint hyperop (n a b : nat) : nat :=
  let fix hyperop_inner (b_inner : nat) : nat :=
     match n, b_inner with
       | O, _       => S b
       | S O,     O => a
       | S (S O), O => 0
       | _, O       => 1
       | S n', S b' => hyperop n' a (hyperop_inner b')
     end
  in hyperop_inner b.

Notation "a [ n ] b" := (hyperop n a b)
  (at level 50, left associativity).


(* Basics *)


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


(* If n = 1, equivalent to addition *)
Theorem hyp1_addition : forall a b,
  a [1] b = a + b.
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

Lemma leq_0_nat:
  forall (n:nat), 0 <= n.
Proof.
  intros n. omega.
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





(* Lemma 2.1
Suppose n > 1. Then a[n]1 = a.
*)
Lemma b1_refl:
  forall (a n : nat), a [S (S n)] 1 = a.
Proof.
  intros a n.
  induction n as [| n' IH ].
  - apply n2_b1_a.
  - rewrite expand_Sn_Sb. apply IH.
Qed.


Theorem b1_n_m:
  forall (n m a : nat), a [S (S n)] 1 = a [S (S m)] 1.
Proof.
  intros n m a.
  repeat rewrite b1_refl. reflexivity.
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

(* Lemma 2.2
Suppose n > 2. Then 1[n]b = 1.
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






(* Chapter 3: Some Basic Inequalities *)

(* Lemma 3.1
 * Suppose c > b > a. Then c > a + 1.
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


(* Section 3.1:
 * A hyper-product is larger than its operands.
 *)

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

Lemma gt_to_exists:
  forall (x y : nat), x > (y+1) -> exists j, x = S (S j).
Proof.
  intros x y H.
(*   exists y. *)
  apply gt_plus1_S_r in H.
Admitted.

(* Lemma 3.2:
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


Lemma hyp_gt_b:
  forall (n a b : nat), S (S a) [n] b > b.
Proof.
  intros n.













