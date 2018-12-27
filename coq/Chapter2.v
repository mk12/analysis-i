(******************************************************************************)
(* Copyright 2018 Mitchell Kember. Subject to the MIT License.                *)
(* Formalization of Analysis I: Chapter 2                                     *)
(******************************************************************************)

(** * Chapter 2: The natural numbers *)

Require Import Common.

(** ** Section 2.1: The Peano axioms *)

(** *** Definition 2.1.1: The natural numbers *)

Inductive N : Set :=
  | O : N
  | S : N → N.

(** *** Axiom 2.1: 0 is a natural number *)

Goal N.
Proof O.

(** *** Axiom 2.2: Every natural number has a successor *)

Goal N → N.
Proof S.

(** *** Definition 2.1.3: Arabic numerals are defined as natural numbers *)

Fixpoint num (n : nat) : N :=
  match n with
  | Datatypes.O => O
  | Datatypes.S m => S (num m)
  end.

(** *** Proposition 2.1.4: 3 is a natural number *)

Goal N.
Proof num 3.

(** *** Axiom 2.3: 0 is not a successor of any natural number *)

Theorem succ_ne_zero {n : N} : S n ≠ O.
Proof. discriminate. Qed.

(** *** Proposition 2.1.6: 4 is not equal to 0 *)

Goal num 4 ≠ O.
Proof succ_ne_zero.

(** *** Axiom 2.4: Different natural numbers have different successors *)

Theorem succ_inj {n m : N} (H : S n = S m) : n = m.
Proof. now injection H. Qed.

(** *** Proposition 2.1.8: 6 is not equal to 2 *)

Goal num 6 ≠ num 2.
Proof mt succ_inj (mt succ_inj succ_ne_zero).

(** *** Axiom 2.5: Principle of mathematical induction *)

Goal ∀ (p : N → Prop) (HO : p O) (HS : ∀ n : N, p n → p (S n)) (n : N), p n.
Proof. now simple induction n. Qed.

(** *** Proposition 2.1.16: Recursive definitions *)

Definition recursive_def (f : N → N → N) (c : N) : N → N :=
  fix a n :=
    match n with
    | O => c
    | S m => f m (a m)
    end.

(** ** Section 2.2: Addition *)

(** *** Definition 2.2.1: Addition of natural numbers *)

Fixpoint add (n m : N) : N :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

Infix "+" := add.

(** *** Lemma 2.2.2 *)  

Theorem add_zero_right {n : N} : n + O = n.
Proof.
  induction n as [|n IHn].
  - show (O + O = O).
    reflexivity.
  - show (S n + O = S n).
    cbn. now rewrite IHn.
Qed.

(** *** Lemma 2.2.3 *)

Theorem add_succ_right {n m : N} : n + S m = S (n + m).
Proof.
  induction n as [|n IHn].
  - show (O + S m = S (O + m)).
    reflexivity.
  - show (S n + S m = S (S n + m)).
    cbn. now rewrite IHn.
Qed.

(** *** Proposition 2.2.4: Addition is commutative *)

Theorem add_comm {n m : N} : n + m = m + n.
Proof.
  induction n as [|n IHn].
  - show (O + m = m + O).
    cbn. now rewrite add_zero_right.
  - show (S n + m = m + S n).
    cbn. now rewrite add_succ_right, IHn.
Qed.

(** *** Proposition 2.2.5: Addition is associative *)

Theorem add_assoc {a b c : N} : (a + b) + c = a + (b + c).
Proof.
  induction a as [|a IHa].
  - show ((O + b) + c = O + (b + c)).
    reflexivity.
  - show ((S a + b) + c = S a + (b + c)).
    cbn. now rewrite IHa.
Qed.

(** *** Proposition 2.2.6: Cancellation law *)

Theorem add_cancel {a b c : N} (H : a + b = a + c) : b = c.
Proof.
  induction a as [|a IHa].
  - given (H : O + b = O + c).
    now cbn in H.
  - given (H : S a + b = S a + c).
    cbn in H. now apply succ_inj, IHa in H.
Qed.

(** Specialize for c = 0: *)

Theorem add_cancel_zero {a b : N} (H : a + b = a) : b = O.
Proof.
  replace a with (a + O) in H at 2 by apply add_zero_right.
  exact (add_cancel H).
Qed.

(** Add to both sides of an equation (undo cancellation): *)

Theorem add_eqn {a b c d : N} (Hab : a = b) (Hcd : c = d) : a + c = b + d.
Proof. now rewrite Hab, Hcd. Qed.

(** *** Definition 2.2.7: Positive natural numbers *)

Definition pos (n : N) : Prop := n ≠ O.

(** *** Proposition 2.2.8 *)

Theorem add_pos {a b : N} (H : pos a) : pos (a + b).
Proof.
  destruct b.
  - show (pos (a + O)).
    now rewrite add_zero_right.
  - show (pos (a + S b)).
    rewrite add_succ_right. exact succ_ne_zero.
Qed.

(** *** Corollary 2.2.9 *)

Theorem add_eq_zero {a b : N} (H : a + b = O) : a = O ∧ b = O.
Proof.
  destruct a.
  - given (H : O + b = O). show (O = O ∧ b = O).
    split. reflexivity. exact H.
  - given (H : S a + b = O). show (S a = O ∧ b = O).
    cbn in H. contradiction (succ_ne_zero H).
Qed.

(** *** Lemma 2.2.10 *)

Theorem pos_pred {a : N} (H : pos a): ∃ b : N, S b = a.
Proof.
  destruct a.
  - given (H : pos O). show (∃ b : N, S b = O).
    contradiction (H eq_refl).
  - given (H : pos (S a)). show (∃ b : N, S b = S a).
    now exists a.
Qed.

(** *** Definition 2.2.11: Ordering of the natural numbers *)

Definition le (n m : N) : Prop := ∃ a : N, m = n + a.
Definition lt (n m : N) : Prop := le n m ∧ n ≠ m.
Definition ge (n m: N) : Prop := le m n.
Definition gt (n m : N) : Prop := lt m n.

Infix "≤" := le.
Infix "<" := lt.
Infix "≥" := ge.
Infix ">" := gt.

(** *** Proposition 2.2.12: Basic properties of order for natural numbers *)

Theorem order_refl {a : N} : a ≥ a.
Proof. exists O. now rewrite add_zero_right. Qed.

Theorem order_trans {a b c : N} : a ≥ b → b ≥ c → a ≥ c.
Proof.
  intros [n Hn] [m Hm].
  exists (m + n).
  now rewrite Hn, Hm, add_assoc.
Qed.

Theorem order_antisymm {a b : N} : a ≥ b → b ≥ a → a = b.
Proof.
  intros [n Hn] [m Hm].
  assert (n = O) as H0. {
    rewrite Hn, add_assoc in Hm.
    now apply eq_sym, add_cancel_zero, add_eq_zero, proj1 in Hm.
  }
  now rewrite Hn, H0, add_zero_right.
Qed.

Theorem ge_iff_add_ge {a b c : N} : a ≥ b ↔ a + c ≥ b + c.
Proof.
  split.
  - show (a ≥ b → a + c ≥ b + c).
    intros [n Hn].
    exists n.
    assert (a + c = b + n + c) as H0 by exact (add_eqn Hn eq_refl).
    now rewrite add_assoc, (@add_comm n c), <-add_assoc in H0.
  - show (a + c ≥ b + c → a ≥ b ).
    intros [n Hn].
    exists n.
    rewrite add_assoc, (@add_comm c n), <-add_assoc in Hn.
    rewrite (@add_comm a c), (@add_comm (b + n) c) in Hn.
    exact (add_cancel Hn).
Qed.

Theorem lt_iff_pos {a b : N} : a < b ↔ ∃ d : N, b = a + d ∧ pos d.
Proof.
  split.
  - show (a < b → ∃ d : N, b = a + d ∧ pos d).
    intros [[n Hn] HNab].
    exists n.
    split.
    + show (b = a + n).
      exact Hn.
    + show (pos n).
      intro HZn.
      rewrite HZn, add_zero_right in Hn.
      assert (a = b) as Hab by exact (symmetry Hn).
      contradiction (HNab Hab).
  - show ((∃ d : N, b = a + d ∧ pos d) → a < b).
    intros [n [Hn HPn]].
    split.
    + show (a ≤ b).
      exists n. exact Hn.
    + show (a ≠ b).
      intro Hab.
      rewrite Hab in Hn.
      assert (n = O) as HZn by exact (add_cancel_zero (eq_sym Hn)).
      contradiction (HPn HZn).
Qed.

Theorem lt_iff_succ_le {a b : N} : a < b ↔ S a ≤ b.
Proof.
  split.
  - show (a < b → S a ≤ b).
    intro HLT.
    destruct (proj1 lt_iff_pos HLT) as [n [Hn HPn]].
    destruct (pos_pred HPn) as [m Hm].
    exists m.
    now rewrite <-Hm, add_succ_right in Hn.
  - show (S a ≤ b → a < b).
    intros [n Hn].
    split.
    + show (a ≤ b).
      exists (S n). now rewrite add_succ_right.
    + show (a ≠ b).
      intro Hab.
      rewrite Hab in Hn.
      cbn in Hn.
      rewrite <-add_succ_right in Hn.
      apply eq_sym, add_cancel_zero in Hn.
      contradiction (succ_ne_zero Hn).
Qed.

(** The following properties are not in the textbook. *)

Theorem lt_succ_iff_le {a b : N} : a < S b ↔ a ≤ b.
Proof.
  split.
  - show (a < S b → a ≤ b).
    intro HLT.
    destruct (proj1 lt_iff_pos HLT) as [n [Hn HPn]].
    destruct (pos_pred HPn) as [m Hm].
    exists m.
    rewrite <-Hm, add_succ_right in Hn.
    exact (succ_inj Hn).
  - show (a ≤ b → a < S b).
    intros [n Hn].
    split.
    + show (a ≤ S b).
      exists (S n).
      rewrite add_succ_right.
      now f_equal.
    + show (a ≠ S b).
      intro HaSb.
      rewrite Hn, <-add_succ_right in HaSb.
      apply eq_sym, add_cancel_zero in HaSb.
      contradiction (succ_ne_zero HaSb).
Qed.

Theorem not_lt_and_ge {a b : N} : ¬ (a < b ∧ a ≥ b).
Proof.
  intros [[[n Hn] HNab] [m Hm]].
  rewrite Hm, add_assoc in Hn.
  apply eq_sym, add_cancel_zero, add_eq_zero, proj1 in Hn.
  rewrite Hn, add_zero_right in Hm.
  contradiction (HNab Hm).
Qed.

Theorem not_le_and_gt {a b : N} : ¬ (a ≤ b ∧ a > b).
Proof.
  intro H.
  apply and_comm in H.
  contradiction (not_lt_and_ge H).
Qed.

Theorem not_lt_zero {a : N} : ¬ (a < O).
Proof.
  intros [[n Hn] HNO].
  apply eq_sym, add_eq_zero, proj1 in Hn.
  contradiction (HNO Hn).
Qed.
