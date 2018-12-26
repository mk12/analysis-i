(******************************************************************************)
(* Copyright 2018 Mitchell Kember. Subject to the MIT License.                *)
(* Formalization of Analysis I: Chapter 2                                     *)
(******************************************************************************)

Set Warnings "-notation-overridden".

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
  | S n' => S (add n' m)
  end.
Infix "+" := add.

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
Theorem add_cancel {a b c : N} (H : a + b = a + c) : b = c.
Proof.
  induction a as [|a IHa].
  - simpl in H. exact H.
  - simpl in H. exact (IHa (succ_inj H)).
Qed.

(** Specialization of Proposition 2.2.6 where c = 0 *)
Theorem add_cancel_zero {a b : N} (H : a + b = a) : b = O.
Proof.
  replace a with (a + O) in H at 2 by apply add_zero_right.
  exact (add_cancel H).
Qed.

(** Add to both sides of an equation **)
Theorem add_eqn {a b c d : N} (Hab : a = b) (Hcd : c = d) : a + c = b + d.
Proof. rewrite Hab, Hcd. reflexivity. Qed.

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
  destruct a.
  - show (O = O ∧ b = O).
    split. reflexivity. exact H.
  - show (S a = O ∧ b = O).
    simpl in H. contradiction (succ_ne_zero H).
Qed.

(** Lemma 2.2.10 *)
Theorem pos_pred {a : N} (H : pos a): ∃ b : N, S b = a.
Proof.
  destruct a.
  - show (∃ b : N, S b = O).
    contradiction H. reflexivity.
  - show (∃ b : N, S b = S a).
    exists a. reflexivity.
Qed.

(** Definition 2.2.11: Ordering of the natural numbers *)
Definition le (n m : N) : Prop := ∃ a : N, m = n + a.
Definition lt (n m : N) : Prop := le n m ∧ n ≠ m.
Definition ge (n m: N) : Prop := le m n.
Definition gt (n m : N) : Prop := lt m n.
Infix "≤" := le.
Infix "<" := lt.
Infix "≥" := ge.
Infix ">" := gt.

(** Proposition 2.2.12: Basic properties of order for natural numbers *)
Section order_properties.
  Context {a b c : N}.

  Theorem order_refl : a ≥ a.
  Proof. exists O. symmetry. exact add_zero_right. Qed.

  Theorem order_trans : a ≥ b → b ≥ c → a ≥ c.
  Proof.
    intros [n Hn] [m Hm].
    exists (m + n).
    rewrite Hn, Hm, add_assoc.
    reflexivity.
  Qed.

  Theorem order_antisymm : a ≥ b → b ≥ a → a = b.
  Proof.
    intros [n Hn] [m Hm].
    assert (n = O) as H0. {
      rewrite Hn, add_assoc in Hm.
      apply eq_sym, add_cancel_zero, add_eq_zero, proj1 in Hm.
      exact Hm.
    }
    rewrite Hn, H0, add_zero_right.
    reflexivity.
  Qed.

  Theorem ge_iff_add_ge : a ≥ b ↔ a + c ≥ b + c.
  Proof.
    split.
    - intros [n Hn].
      exists n.
      assert (a + c = b + n + c) as H0 by apply (add_eqn Hn eq_refl).
      rewrite add_assoc, (@add_comm n c), <-add_assoc in H0.
      exact H0.
    - intros [n Hn].
End order_properties.