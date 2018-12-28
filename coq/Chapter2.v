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
Proof N_ind.

(** With induction, we can show that no natural number equals its successor: *)

Theorem succ_ne_self {n : N} : S n ≠ n.
Proof.
  induction n as [|n IHn].
  - show (S O ≠ O).
    exact succ_ne_zero.
  - given (IHn : S n ≠ n). show (S (S n) ≠ S n).
    apply (mt succ_inj). exact IHn.
Qed.

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

Theorem add_zero_right (n : N) : n + O = n.
Proof.
  induction n as [|n IHn].
  - show (O + O = O).
    reflexivity.
  - given (IHn : n + O = n). show (S n + O = S n).
    cbn. now rewrite IHn.
Qed.

(** *** Lemma 2.2.3 *)

Theorem add_succ_right (n m : N) : n + S m = S (n + m).
Proof.
  induction n as [|n IHn].
  - show (O + S m = S (O + m)).
    reflexivity.
  - given (n + S m = S (n + m)). show (S n + S m = S (S n + m)).
    cbn. now rewrite IHn.
Qed.

(** *** Proposition 2.2.4: Addition is commutative *)

Theorem add_comm (n m : N) : n + m = m + n.
Proof.
  induction n as [|n IHn].
  - show (O + m = m + O).
    cbn. now rewrite add_zero_right.
  - given (n + m = m + n). show (S n + m = m + S n).
    cbn. now rewrite add_succ_right, IHn.
Qed.

(** *** Proposition 2.2.5: Addition is associative *)

Theorem add_assoc (a b c : N) : (a + b) + c = a + (b + c).
Proof.
  induction a as [|a IHa].
  - show ((O + b) + c = O + (b + c)).
    reflexivity.
  - given (IHa : (a + b) + c = a + (b + c)).
    show ((S a + b) + c = S a + (b + c)).
    cbn. now rewrite IHa.
Qed.

(** *** Proposition 2.2.6: Cancellation law *)

Theorem add_cancel {a b c : N} (H : a + b = a + c) : b = c.
Proof.
  induction a as [|a IHa].
  - given (H : O + b = O + c).
    now cbn in H.
  - given (H : S a + b = S a + c) (IHa : a + b = a + c → b = c).
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
  destruct b as [|b].
  - show (pos (a + O)).
    now rewrite add_zero_right.
  - show (pos (a + S b)).
    rewrite add_succ_right. exact succ_ne_zero.
Qed.

(** *** Corollary 2.2.9 *)

Theorem add_eq_zero {a b : N} (H : a + b = O) : a = O ∧ b = O.
Proof.
  destruct a as [|a].
  - given (H : O + b = O). show (O = O ∧ b = O).
    split. reflexivity. exact H.
  - given (H : S a + b = O). show (S a = O ∧ b = O).
    cbn in H. contradiction (succ_ne_zero H).
Qed.

(** *** Lemma 2.2.10 *)

Theorem pos_pred {a : N} (H : pos a): ∃ b : N, S b = a.
Proof.
  destruct a as [|a].
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

(** Order is reflexive: *)

Theorem order_refl {a : N} : a ≥ a.
Proof. exists O. now rewrite add_zero_right. Qed.

(** Order is transitive: *)

Theorem order_trans {a b c : N} : a ≥ b → b ≥ c → a ≥ c.
Proof.
  intros [n Hn] [m Hm].
  exists (m + n).
  now rewrite Hn, Hm, add_assoc.
Qed.

(** Order is anti-symmetric: *)

Theorem order_antisymm {a b : N} : a ≥ b → b ≥ a → a = b.
Proof.
  intros [n Hn] [m Hm].
  assert (n = O) as H0. {
    rewrite Hn, add_assoc in Hm.
    now apply eq_sym, add_cancel_zero, add_eq_zero, proj1 in Hm.
  }
  now rewrite Hn, H0, add_zero_right.
Qed.

(** Addition preserves order: *)

Theorem order_iff_add {a b c : N} : a ≥ b ↔ a + c ≥ b + c.
Proof.
  split.
  - show (a ≥ b → a + c ≥ b + c).
    intros [n Hn].
    exists n.
    have (a + c = b + n + c) as H0 from (add_eqn Hn eq_refl).
    now rewrite add_assoc, (add_comm n c), <-add_assoc in H0.
  - show (a + c ≥ b + c → a ≥ b).
    intros [n Hn].
    exists n.
    rewrite add_assoc, (add_comm c n), <-add_assoc in Hn.
    rewrite (add_comm a c), (add_comm (b + n) c) in Hn.
    exact (add_cancel Hn).
Qed.

(** Extra properties: *)

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
      have (a = b) as Hab from (symmetry Hn).
      contradiction (HNab Hab).
  - show ((∃ d : N, b = a + d ∧ pos d) → a < b).
    intros [n [Hn HPn]].
    split.
    + show (a ≤ b).
      exists n. exact Hn.
    + show (a ≠ b).
      intro Hab.
      rewrite Hab in Hn.
      have (n = O) as HZn from (add_cancel_zero (eq_sym Hn)).
      contradiction (HPn HZn).
Qed.

Theorem lt_iff_succ_le {a b : N} : a < b ↔ S a ≤ b.
Proof.
  split.
  - show (a < b → S a ≤ b).
    intro HLT.
    destruct (iff_mp lt_iff_pos HLT) as [n [Hn HPn]].
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

(** The following properties are not listed in the textbook. *)

Theorem ge_zero {a : N} : a ≥ O.
Proof. now exists a. Qed.

Theorem succ_gt_zero {a : N} : S a > O.
Proof. split. exact ge_zero. exact (not_eq_sym succ_ne_zero). Qed.

Theorem not_lt_zero {a : N} : ¬ (a < O).
Proof.
  intros [[n Hn] HNO].
  apply eq_sym, add_eq_zero, proj1 in Hn.
  contradiction (HNO Hn).
Qed.

Theorem lt_succ_iff_le {a b : N} : a < S b ↔ a ≤ b.
Proof.
  split.
  - show (a < S b → a ≤ b).
    intro HLT.
    destruct (iff_mp lt_iff_pos HLT) as [n [Hn HPn]].
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

Theorem le_iff_eq_or_lt {a b : N} : a ≤ b ↔ a = b ∨ a < b.
Proof.
  split.
  - show (a ≤ b → a = b ∨ a < b).
    intro HLE.
    destruct (HLE) as [n Hn].
    destruct n as [|n].
    + left. show (a = b).
      now rewrite add_zero_right in Hn.
    + right. show (a < b).
      split.
      * show (a ≤ b).
        exact HLE.
      * show (a ≠ b).
        intro HSab.
        rewrite HSab in Hn.
        apply eq_sym, add_cancel_zero in Hn.
        contradiction (succ_ne_zero Hn).
  - show (a = b ∨ a < b → a ≤ b).
    intros [HEQ | HLT].
    + given (HEQ : a = b).
      rewrite HEQ. exact order_refl.
    + given (HLT : a < b).
      exact (proj1 HLT).
Qed.

(** *** Proposition 2.2.13: Trichotomy of order for natural numbers *)

(** First, we show that _at least_ one of [lt], [eq], and [gt] holds. *)

Theorem trichotomy (a b : N) : a < b ∨ a = b ∨ a > b.
Proof.
  induction a as [|a IHa].
  - show (O < b ∨ O = b ∨ O > b).
    destruct b as [|b].
    + right. left. show (O = O).
      reflexivity.
    + left. show (O < S b).
      split.
      * show (O ≤ S b).
        exact ge_zero.
      * show (O ≠ S b).
        apply not_eq_sym. exact succ_ne_zero.
  - given (IHa : a < b ∨ a = b ∨ a > b). show (S a < b ∨ S a = b ∨ S a > b).
    destruct IHa as [HLT | [HEQ | HGT]].
    + given (HLT : a < b).
      apply or_assoc, or_introl, or_comm.
      show (S a = b ∨ S a < b).
      have (S a ≤ b) as HSLE from (iff_mp lt_iff_succ_le HLT).
      exact (iff_mp le_iff_eq_or_lt HSLE).
    + given (HEQ : a = b). right. right. show (S a > b).
      split.
      * show (b ≤ S a).
        exists (S O). now rewrite HEQ, add_succ_right, add_zero_right.
      * show (b ≠ S a).
        rewrite HEQ. apply not_eq_sym, succ_ne_self.
    + given (HGT : a > b). right. right. show (S a > b).
      destruct HGT as [[n Hn] HNba].
      split.
      * show (b ≤ S a).
        exists (S n).
        rewrite add_succ_right.
        now f_equal.
      * show (b ≠ S a).
        intro HbSa.
        rewrite HbSa in Hn.
        cbn in Hn.
        rewrite <-add_succ_right in Hn.
        apply eq_sym, add_cancel_zero in Hn.
        contradiction (succ_ne_zero Hn).
Qed.

(** Next, we use [trichotomy] to prove the dichotomy of [le] and [gt], along
    with some related properties. *)

Theorem dichotomy (a b : N) : a ≤ b ∨ a > b.
Proof.
  destruct (trichotomy a b) as [HLT | [HEQ | HGT]].
  - given (HLT : a < b). left. show (a ≤ b).
    exact (proj1 HLT).
  - given (HEQ : a = b). left. show (a ≤ b).
    rewrite HEQ. exact order_refl.
  - given (HGT : a > b). right. show (a > b).
    exact HGT.
Qed.

Theorem not_le_and_gt {a b : N} : ¬ (a ≤ b ∧ a > b).
Proof.
  intros [[n Hn] [[m Hm] HNba]].
  rewrite Hn, add_assoc in Hm.
  apply eq_sym, add_cancel_zero, add_eq_zero, proj1 in Hm.
  rewrite Hm, add_zero_right in Hn.
  contradiction (HNba Hn).
Qed.

Theorem le_iff_not_gt {a b : N} : a ≤ b ↔ ¬ a > b.
Proof.
  split.
  - show (a ≤ b → ¬ a > b).
    intros HLE HGT.
    contradiction (not_le_and_gt (conj HLE HGT)).
  - show (¬ a > b → a ≤ b).
    intro HNGT.
    destruct (dichotomy a b) as [HLE | HGT].
    + given (HLE : a ≤ b).
      exact HLE.
    + given (HGT : a > b).
      contradiction (HNGT HGT).
Qed.

Theorem lt_iff_not_ge {a b : N} : a < b ↔ ¬ a ≥ b.
Proof.
  split.
  - show (a < b → ¬ a ≥ b).
    intro HLT.
    now apply not_not, (iff_mtr le_iff_not_gt) in HLT.
  - show (¬ a ≥ b → a < b).
    intros HNGE.
    destruct (dichotomy b a) as [HGE | HLT].
    + given (HGE : a ≥ b).
      contradiction (HNGE HGE).
    + given (HLT : a < b).
      exact HLT.
Qed.

(** Finally, we that _at most_ one of [lt], [eq], and [gt] holds. This completes
    the proof of trichotomy, which requires that _exactly_ one holds. *)

Theorem not_eq_and_lt {a b : N} : ¬ (a = b ∧ a < b).
Proof.
  intros [Hab [_ HNab]].
  contradiction (HNab Hab).
Qed.

Theorem not_eq_and_gt {a b : N} : ¬ (a = b ∧ a > b).
Proof.
  intros [Hab [_ HNba]].
  contradiction (HNba (eq_sym Hab)).
Qed.

Theorem not_lt_and_gt {a b : N} : ¬ (a < b ∧ a > b).
Proof.
  intros [[HLE _] HGT].
  contradiction (not_le_and_gt (conj HLE HGT)).
Qed.

(** *** Proposition 2.2.14: Strong principle of induction *)

Section strong_induction.
  Variables (n0 : N) (p : N → Prop).

  Let q (n : N) : Prop := ∀ m : N, m ≥ n0 ∧ m < n → p m.

  Theorem strong_induction (SI : ∀ n : N, n ≥ n0 → q n → p n) (n : N)
    (H : n ≥ n0) : p n.
  Proof.
    enough (q n) as H0 by exact (SI n H H0).
    induction n as [|n IHn].
    - given (H : O ≥ n0). show (∀ m : N, m ≥ n0 ∧ m < O → p m).
      intros m [_ HmLTO].
      contradiction (not_lt_zero HmLTO).
    - given (H : S n ≥ n0). show (∀ m : N, m ≥ n0 ∧ m < S n → p m).
      intros m [HmGE HmLT].
      assert (m ≤ n) as HmLEn by now apply lt_succ_iff_le in HmLT.
      have (n ≥ n0) as HnGE from (order_trans HmLEn HmGE).
      have (q n) as Hqn from (IHn HnGE).
      have (p n) as Hpn from (SI n HnGE Hqn).
      destruct (dichotomy n m) as [HmGEn | HmLTn].
      + given (HmGEn : m ≥ n).
        have (n = m) as HEQ from (order_antisymm HmLEn HmGEn).
        now rewrite HEQ in Hpn.
      + given (HmLTn : m < n).
        exact (Hqn m (conj HmGE HmLTn)).
  Qed.
End strong_induction.

(** *** Exercise 2.2.6: Backward principle of induction *)

Theorem backward_induction (n : N) (p : N → Prop) (BI : ∀ m : N, p (S m) → p m)
  (Hp : p n) (m : N) (Hmn : m ≤ n): p m.
Proof.
  intros.
  induction n as [|n IHn].
  - given (Hp : p O) (Hmn : m ≤ O).
    have (m = O) as HmO from (order_antisymm ge_zero Hmn).
    now rewrite HmO.
  - given (Hp : p (S n)) (Hmn : m ≤ S n).
    destruct (dichotomy m n) as [HLE | HGT].
    + given (HLE : m ≤ n).
      have (p n) as Hpn from (BI n Hp).
      exact (IHn Hpn HLE).
    + given (HGT : m > n).
      have (m ≥ S n) as HGE from (iff_mp lt_iff_succ_le HGT).
      have (m = S n) as HSn from (order_antisymm HGE Hmn).
      now rewrite HSn.
Qed.

(** ** Section 2.3: Multiplication *)

(** *** Definition 2.3.1: Multiplication of natural numbers *)

Fixpoint mul (n m : N) : N :=
  match n with
  | O => O
  | S n' => mul n' m + m
  end.

Infix "*" := mul.

(** *** Exercise 2.3.1 *)

Theorem mul_zero_right {n : N} : n * O = O.
Proof.
  induction n as [|n IHn].
  - show (O * O = O).
    reflexivity.
  - given (IHn : n * O = O). show (S n * O = O).
    cbn. now rewrite IHn.
Qed.

Theorem mul_succ_right {n m : N} : n * S m = n * m + n.
Proof.
  induction n as [|n IHn].
  - show (O * S m = O * m + O).
    reflexivity.
  - given (IHn : n * S m = n * m + n). show (S n * S m = S n * m + S n).
    cbn.
    rewrite add_assoc.
    replace (m + S n) with (n + S m) by now rewrite 2 add_succ_right, add_comm.
    rewrite <-add_assoc.
    exact (add_eqn IHn eq_refl).
Qed.

(** *** Lemma 2.3.2: Multiplication is commutative *)

Theorem mul_comm {n m : N} : n * m = m * n.
Proof.
  induction n as [|n IHn].
  - show (O * m = m * O).
    cbn. now rewrite mul_zero_right.
  - given (IHn : n * m = m * n). show (S n * m = m * S n).
    cbn. now rewrite mul_succ_right, IHn.
Qed.
