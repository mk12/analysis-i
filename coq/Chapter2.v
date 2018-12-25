(******************************************************************************)
(* Copyright 2018 Mitchell Kember. Subject to the MIT License.                *)
(* Formalization of Analysis I: Chapter 2                                     *)
(******************************************************************************)

Require Import Common.

(** Definition 2.1.1: The natural numbers *)
Inductive N : Set :=
  | O : N
  | S : N → N.

(** Axiom 2.1: 0 is a natural number *)
Goal N.
Proof O.

(** Axiom 2.2: Every natural number has a successor *)
Goal N → N.
Proof S.

(** Definition 2.1.3: Arabic numerals are defined as natural numbers *)
Fixpoint num (n : nat) : N :=
  match n with
  | Datatypes.O => O
  | Datatypes.S m => S (num m)
  end.

(** Proposition 2.1.4: 3 is a natural number *)
Goal N.
Proof num 3.

(** Axiom 2.3: 0 is not a successor of any natural number *)
Theorem succ_ne_zero {n : N} : S n ≠ O.
Proof. discriminate. Qed.

(** Proposition 2.1.6: 4 is not equal to 0 *)
Goal num 4 ≠ O.
Proof succ_ne_zero.

(** Axiom 2.4: Different natural numbers have different successors *)
Theorem succ_inj {n m : N} (H : S n = S m) : n = m.
Proof. injection H. trivial. Qed.

(** Proposition 2.1.8: 6 is not equal to 2 *)
Goal num 6 ≠ num 2.
Proof mt succ_inj (mt succ_inj succ_ne_zero).

(** Axiom 2.5: Principle of mathematical induction *)
Goal ∀ (p : N → Prop) (HO : p O) (HS : ∀ n : N, p n → p (S n)) (n : N), p n.
Proof.
  induction n as [|n IHn].
  - show (p O). exact HO.
  - show (p (S n)). exact (HS n IHn).
Qed.

(** Proposition 2.1.16: Recursive definitions *)
Definition recursive_def (f : N → N → N) (c : N) : N → N :=
  fix a n :=
    match n with
    | O => c
    | S m => f m (a m)
    end.

(** Definition 2.2.1: Addition of natural numbers *)
Fixpoint add (n m : N) : N :=
  match n with
  | O => m
  | S n' => S (n' + m)
  end
where "x + y" := (add x y).

(** Lemma 2.2.2 *)
Theorem add_zero_right {n : N} : n + O = n.
Proof.
  induction n as [|n IHn].
  - show (O + O = O).
    simpl. reflexivity.
  - show (S n + O = S n).
    simpl. rewrite IHn. reflexivity.
Qed.

(** Lemma 2.2.3 *)
Theorem add_succ_right {n m : N} : n + S m = S (n + m).
Proof.
  induction n as [|n IHn].
  - show (O + S m = S (O + m)).
    simpl. reflexivity.
  - show (S n + S m = S (S n + m)).
    simpl. rewrite IHn. reflexivity.
Qed.

(** Proposition 2.2.4: Addition is commutative *)
Theorem add_comm {n m : N} : n + m = m + n.
Proof.
  induction n as [|n IHn].
  - show (O + m = m + O).
    simpl. rewrite add_zero_right. reflexivity.
  - show (S n + m = m + S n).
    simpl. rewrite add_succ_right, IHn. reflexivity.
Qed.

(** Proposition 2.2.5: Addition is associative *)
Theorem add_assoc {a b c : N} : (a + b) + c = a + (b + c).
Proof.
  induction a as [|a IHa].
  - show ((O + b) + c = O + (b + c)).
    simpl. reflexivity.
  - show ((S a + b) + c = S a + (b + c)).
    simpl. rewrite IHa. reflexivity.
Qed.


(** Proposition 2.2.6: Cancellation law *)
Theorem add_cancel2 {a b c : N} (H : a + b = a + c) : b = c.
Proof.
  induction a as [|a IHa].
  - simpl in H. exact H.
  - simpl in H. exact (IHa (succ_inj H)).
Qed.

(** Proposition 2.2.6: Cancellation law *)
Theorem add_cancel {a b c : N} : a + b = a + c → b = c.
Proof.
  induction a as [|a IHa].
  - show (O + b = O + c → b = c).
    simpl. trivial.
  - show (S a + b = S a + c → b = c).
    intro H. simpl in H. exact (IHa (succ_inj H)).
Qed.

(** Definition 2.2.7: Positive natural numbers *)
Definition pos (n : N) : Prop := n ≠ O.

(** Proposition 2.2.8 *)
Theorem add_pos {a b : N} (H : pos a) : pos (a + b).
Proof.
  destruct b.
  - show (pos (a + O)).
    rewrite add_zero_right. exact H.
  - show (pos (a + S b)).
    rewrite add_succ_right. exact succ_ne_zero.
Qed.

(** Corollary 2.2.9 *)
Theorem add_eq_zero {a b : N} (H : a + b = O) : a = O ∧ b = O.
Proof.
  induction a as [|a IHa].
  - show (O = O ∧ b = O).
    split. reflexivity. exact H.
  - show (S a = O ∧ b = O).
    simpl in H. contradiction (succ_ne_zero H).
Qed.

(** Lemma 2.2.10 *)
Theorem pos_pred {a : N} (H : pos a): ∃ b : N, S b = a.
Proof.
  induction a as [|a Ha].
  - show (exists b : N, S b = 0).
 