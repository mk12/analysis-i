-- Copyright 2017 Mitchell Kember. Subject to the MIT License.
-- Formalization of Analysis I: Chapter 2

import .common

open classical (by_cases by_contradiction)
open eq (symm)

-- Definition 2.1.1: The natural numbers
inductive N : Type
  | zero : N
  | succ : N → N

namespace N
  -- Type class instance
  instance : has_zero N := ⟨zero⟩

  -- Axiom 2.1: 0 is a natural number
  example : N := 0

  -- Axiom 2.2: Every natural number has a successor
  example (n : N) : N := succ n

  -- Definition 2.1.3: Arabic numerals are defined as natural numbers
  def num : nat → N
    | 0 := 0
    | (nat.succ n) := succ (num n)

  -- Proposition 2.1.4: 3 is a natural number
  example : N := num 3

  -- Axiom 2.3: 0 is not a successor of any natural number
  theorem succ_ne_zero {n : N} : succ n ≠ 0 :=
    suppose succ n = 0, N.no_confusion this

  -- Proposition 2.1.6: 4 is not equal to 0
  example : num 4 ≠ 0 := succ_ne_zero

  -- Axiom 2.4: Different natural numbers have different successors
  theorem succ_inj {n m : N} : succ n = succ m → n = m :=
    succ.inj

  -- Proposition 2.1.8: 6 is not equal to 2
  example : num 6 ≠ num 2 :=
    have num 4 ≠ num 0, from succ_ne_zero,
    have num 5 ≠ num 1, from mt succ_inj this,
    show num 6 ≠ num 2, from mt succ_inj this

  -- Axiom 2.5: Principle of mathematical induction
  theorem induction {p : N → Prop} : p 0 → (∀ n : N, p n → p (succ n)) →
      ∀ n : N, p n :=
    N.rec

  -- More convenient form of Axiom 2.5
  open N (renaming rec_on → induction_on)

  -- Proposition 2.1.16: Recursive definitions
  section recursive_def
    parameters (f : N → N → N) (c : N)

    private def a (n : N) : N := N.rec c f n

    example : a 0 = c := rfl
    example (n : N) : a (succ n) = f n (a n) := rfl
  end recursive_def

  -- Definition 2.2.1: Addition of natural numbers
  def add : N → N → N
    | 0 m := m
    | (succ n) m := succ (add n m)

  -- Type class instance
  instance : has_add N := ⟨add⟩

  -- Lemma 2.2.2
  lemma add_zero_right {n : N} : n + 0 = n :=
    induction_on n
      (show zero + 0 = 0, from rfl) -- can't use 0 for some reason
      (assume (n : N), assume (IH : n + 0 = n),
        show succ n + 0 = succ n, from calc
          succ n + 0 = succ (n + 0) : rfl
          ... = succ n : by rw IH)

  -- Lemma 2.2.3
  lemma add_succ_right {n m : N} : n + succ m = succ (n + m) :=
    induction_on n
      (show 0 + succ m = succ (0 + m), from calc
        0 + succ m = succ m : rfl
        ... = succ (0 + m) : rfl)
      (assume (n : N) (IH : n + succ m = succ (n + m)),
        show succ n + succ m = succ (succ n + m), from calc
          succ n + succ m = succ (n + succ m) : rfl
          ... = succ (succ (n + m)) : by rw IH
          ... = succ (succ n + m) : rfl)

  -- Proposition 2.2.4: Addition is commutative
  theorem add_comm {n m : N} : n + m = m + n :=
    induction_on n
      (show 0 + m = m + 0, from calc
        0 + m = m : rfl
        ... = m + 0 : add_zero_right.symm)
      (assume (n : N) (IH : n + m = m + n),
        show succ n + m = m + succ n, from calc
          succ n + m = succ (n + m) : rfl
          ... = succ (m + n) : by rw IH
          ... = m + succ n : add_succ_right.symm)

  -- Proposition 2.2.5: Addition is associative
  theorem add_assoc {a b c : N} : (a + b) + c = a + (b + c) :=
    induction_on a
      (show (0 + b) + c = 0 + (b + c), from calc
        (0 + b) + c = b + c : rfl
        ... = 0 + (b + c) : rfl)
      (assume (a : N) (IH : (a + b) + c = a + (b + c)),
        show (succ a + b) + c = succ a + (b + c), from calc
          (succ a + b) + c = succ (a + b) + c : rfl
          ... = succ ((a + b) + c) : rfl
          ... = succ (a + (b + c)) : by rw IH
          ... = succ a + (b + c) : rfl)

  -- Proposition 2.2.6: Cancellation law
  theorem add_cancel {a b c : N} : a + b = a + c → b = c :=
    induction_on a
      (suppose 0 + b = 0 + c,
        show b = c, from calc
          b = 0 + b : rfl
          ... = 0 + c : this
          ... = c : rfl)
      (assume (a : N) (IH : a + b = a + c → b = c),
        suppose succ a + b = succ a + c,
        have succ (a + b) = succ (a + c), from calc
          succ (a + b) = succ a + b : rfl
          ... = succ a + c : this
          ... = succ (a + c) : rfl,
        have a + b = a + c, from succ_inj this,
        show b = c, from IH this)

  -- Definition 2.2.7: Positive natural numbers
  def pos (n : N) : Prop := n ≠ 0

  -- Proposition 2.2.8
  theorem add_pos {a b : N} (H : pos a) : pos (a + b) :=
    induction_on b
      (show pos (a + 0), by rw add_zero_right; exact H)
      (assume (b : N) (IH : pos (a + b)),
        have pos (succ (a + b)), from succ_ne_zero,
        show pos (a + succ b), by rw add_succ_right; exact this)

  -- Corollary 2.2.9
  theorem add_eq_zero {a b : N} (H : a + b = 0) : a = 0 ∧ b = 0 :=
    by_cases
      (assume Ha : a = 0,
        have b = 0, by rw Ha at H; exact H,
        show a = 0 ∧ b = 0, from ⟨Ha, this⟩)
      (suppose a ≠ 0,
        have pos (a + b), from add_pos this,
        absurd H this)

  -- Lemma 2.2.10
  lemma pos_pred {a : N} : pos a → ∃ b : N, succ b = a :=
    induction_on a
      (suppose pos 0, absurd rfl this)
      (assume (a : N) (IH : pos a → ∃ b : N, succ b = a) (H : pos (succ a)),
        show ∃ b : N, succ b = succ a, from ⟨a, rfl⟩)

  -- Definition 2.2.11: Ordering of the natural numbers
  def le (n m : N) : Prop := ∃ a : N, m = n + a
  def lt (n m : N) : Prop := le n m ∧ n ≠ m

  -- Type class instances
  instance : has_le N := ⟨le⟩
  instance : has_lt N := ⟨lt⟩

  -- Proposition 2.2.12: Basic properties of order for natural numbers
  section order_properties
    variables {a b c : N}

    theorem order_refl : a ≥ a :=
      ⟨0, add_zero_right.symm⟩

    theorem order_trans : a ≥ b → b ≥ c → a ≥ c
      | ⟨n, (Hn : a = b + n)⟩ ⟨m, (Hm : b = c + m)⟩ :=
        have a = c + (m + n), from calc
          a = b + n : Hn
          ... = c + m + n : by rw Hm
          ... = c + (m + n) : add_assoc,
        show a ≥ c, from ⟨m + n, this⟩

    theorem order_antisymm : a ≥ b → b ≥ a → a = b
      | ⟨n, (Hn : a = b + n)⟩ ⟨m, (Hm : b = a + m)⟩ :=
        have a + 0 = a + (m + n), from calc
          a + 0 = a : add_zero_right
          ... = b + n : Hn
          ... = a + m + n : by rw Hm
          ... = a + (m + n) : add_assoc,
        have m + n = 0, from add_cancel this.symm,
        have m = 0 ∧ n = 0, from add_eq_zero this,
        show a = b, from calc
          a = b + n : Hn
          ... = b + 0 : by rw this.right
          ... = b : add_zero_right

    theorem ge_iff_add_ge : a ≥ b ↔ a + c ≥ b + c :=
      iff.intro
        (suppose a ≥ b,
          let ⟨n, (H : a = b + n)⟩ := this in
          have a + c = b + c + n, from calc
            a + c = b + n + c : by rw H
            ... = b + (n + c) : add_assoc
            ... = b + (c + n) : by rw @add_comm n c
            ... = b + c + n : add_assoc.symm,
          show a + c ≥ b + c, from ⟨n, this⟩)
        (suppose a + c ≥ b + c,
          let ⟨n, (H : a + c = b + c + n)⟩ := this in
          have c + a = c + (b + n), from calc
            c + a = a + c : add_comm
            ... = b + c + n : H
            ... = c + b + n : by rw @add_comm b c
            ... = c + (b + n) : add_assoc,
          have a = b + n, from add_cancel this,
          show a ≥ b, from ⟨n, this⟩)

    theorem lt_iff_pos : a < b ↔ ∃ d : N, b = a + d ∧ pos d :=
      iff.intro
        (suppose a < b,
          have H : a ≤ b ∧ a ≠ b, from this,
          let ⟨d, (Hd : b = a + d)⟩ := H.left in
          have pos d, from
            suppose d = 0,
            have b = a, from calc
              b = a + d : Hd
              ... = a + 0 : by rw this
              ... = a : add_zero_right,
            absurd this.symm H.right,
          show ∃ d : N, b = a + d ∧ pos d, from
            ⟨d, ⟨Hd, this⟩⟩)
        (suppose ∃ d : N, b = a + d ∧ pos d,
          let ⟨d, (H : b = a + d ∧ pos d)⟩ := this in
          have H₁ : a ≤ b, from ⟨d, H.left⟩,
          have H₂ : a ≠ b, from
            suppose a = b,
            have b + 0 = b + d, from calc
              b + 0 = b : add_zero_right
              ... = a + d : H.left
              ... = b + d : by rw this,
            have 0 = d, from add_cancel this,
            absurd this.symm H.right,
          show a < b, from ⟨H₁, H₂⟩)

    theorem lt_iff_succ_le : a < b ↔ succ a ≤ b :=
      iff.intro
        (suppose a < b,
          let
            ⟨d, (H₁ : b = a + d ∧ pos d)⟩ := lt_iff_pos.mp this,
            ⟨d', (H₂ : succ d' = d)⟩ := pos_pred H₁.right
          in
          have b = succ a + d', from calc
            b = a + d : H₁.left
            ... = a + succ d' : by rw H₂
            ... = succ (a + d') : add_succ_right
            ... = succ a + d' : rfl,
          show succ a ≤ b, from ⟨d', this⟩)
        (suppose succ a ≤ b,
          let ⟨n, (H : b = succ a + n)⟩ := this in
          have b = a + succ n, from calc
            b = succ a + n : H
            ... = succ (a + n) : rfl
            ... = a + succ n : add_succ_right.symm,
          have H₁ : a ≤ b, from ⟨succ n, this⟩,
          have H₂ : a ≠ b, from
            suppose a = b,
            have a + 0 = a + succ n, from calc
              a + 0 = a : add_zero_right
              ... = b : this
              ... = succ a + n : H
              ... = succ (a + n) : rfl
              ... = a + succ n : add_succ_right.symm,
            have 0 = succ n, from add_cancel this,
            absurd this.symm succ_ne_zero,
          show a < b, from ⟨H₁, H₂⟩)

    -- Extra properties

    theorem lt_succ_iff_le : a < succ b ↔ a ≤ b :=
      iff.intro
        (suppose a < succ b,
          let
            ⟨d, (H₁ : succ b = a + d ∧ pos d)⟩ := lt_iff_pos.mp this,
            ⟨d', (H₂ : succ d' = d)⟩ := pos_pred H₁.right
          in
          have succ b = succ (a + d'), from calc
            succ b = a + d : H₁.left
            ... = a + succ d' : by rw H₂
            ... = succ (a + d') : add_succ_right,
          have b = a + d', from succ_inj this,
          show a ≤ b, from ⟨d', this⟩)
        (suppose a ≤ b,
          let ⟨n, (H : b = a + n)⟩ := this in
          have succ b = a + succ n, from calc
            succ b = succ (a + n) : by rw H
            ... = a + succ n : add_succ_right.symm,
          have H₁ : a ≤ succ b, from ⟨succ n, this⟩,
          have H₂ : a ≠ succ b, from
            suppose a = succ b,
            have b + 0 = b + succ n, from calc
              b + 0 = b : add_zero_right
              ... = a + n : H
              ... = succ b + n : by rw this
              ... = succ (b + n) : rfl
              ... = b + succ n : add_succ_right.symm,
            have 0 = succ n, from add_cancel this,
            absurd this.symm succ_ne_zero,
          show a < succ b, from ⟨H₁, H₂⟩)

    theorem not_lt_and_ge : ¬ (a < b ∧ a ≥ b) :=
      assume H : a < b ∧ a ≥ b,
      let
        ⟨n, (Hn : b = a + n)⟩ := H.left.left,
        ⟨m, (Hm : a = b + m)⟩ := H.right
      in
      have H₁ : a ≠ b, from H.left.right,
      have a + 0 = a + (n + m), from calc
        a + 0 = a : add_zero_right
        ... = b + m : Hm
        ... = a + n + m : by rw Hn
        ... = a + (n + m) : add_assoc,
      have 0 = n + m, from add_cancel this,
      have m = 0, from (add_eq_zero this.symm).right,
      have a = b, from calc
        a = b + m : Hm
        ... = b + 0 : by rw this
        ... = b : add_zero_right,
      absurd this H₁

    theorem not_le_and_gt : ¬ (a ≤ b ∧ a > b) :=
      suppose a ≤ b ∧ a > b,
      have b < a ∧ b ≥ a, from this.swap,
      absurd this (@not_lt_and_ge b a)

    theorem not_lt_zero : ¬ (a < 0) :=
      suppose a < 0,
      let ⟨n, (H : 0 = a + n)⟩ := this.left in
      have H₁ : a ≠ 0, from this.right,
      have H₂ : a = 0, from (add_eq_zero H.symm).left,
      absurd H₂ H₁
  end order_properties

  -- Proposition 2.2.13: Trichotomy of order for natural numbers
  section trichotomy
    variables {a b : N}

    theorem trichotomy : a < b ∨ a = b ∨ a > b :=
      induction_on a
        (show 0 < b ∨ 0 = b ∨ 0 > b, from
          have H : 0 ≤ b, from ⟨b, rfl⟩,
          by_cases
            (suppose 0 = b, or.inr (or.inl this))
            (suppose 0 ≠ b, or.inl ⟨H, this⟩))
        (assume (a : N) (IH : a < b ∨ a = b ∨ a > b),
          show succ a < b ∨ succ a = b ∨ succ a > b, from IH.elim3
            (suppose a < b,
              have H : succ a ≤ b, from lt_iff_succ_le.mp this,
              by_cases
                (suppose succ a = b, or.inr (or.inl this))
                (suppose succ a ≠ b, or.inl ⟨H, this⟩))
            (suppose a = b,
              have H₁ : succ a = b + succ 0, from calc
                succ a = succ b : by rw this
                ... = succ b + 0 : add_zero_right.symm
                ... = succ (b + 0) : rfl
                ... = b + succ 0 : add_succ_right.symm,
              have H₂ : b ≠ succ a, from
                suppose b = succ a,
                have b + 0 = b + succ 0, from calc
                  b + 0 = b : add_zero_right
                  ... = succ a : this
                  ... = b + succ 0 : H₁,
                have 0 = succ 0, from add_cancel this,
                absurd this.symm succ_ne_zero,
              have succ a ≥ b, from ⟨succ 0, H₁⟩,
              have succ a > b, from ⟨this, H₂⟩,
              show succ a < b ∨ succ a = b ∨ succ a > b, from
                or.inr (or.inr this))
            (suppose a > b,
              let ⟨n, (Hn : a = b + n)⟩ := this.left in
              have b ≠ a, from this.right,
              have H₁ : succ a = b + succ n, from calc
                succ a = succ (b + n) : by rw Hn
                ... = b + succ n : add_succ_right.symm,
              have H₂ : b ≠ succ a, from
                suppose b = succ a,
                have succ a + 0 = succ a + succ n, from calc
                  succ a + 0 = b + succ n + 0 : by rw H₁
                  ... = b + succ n : add_zero_right
                  ... = succ a + succ n : by rw this,
                have 0 = succ n, from add_cancel this,
                absurd this.symm succ_ne_zero,
              have succ a ≥ b, from ⟨succ n, H₁⟩,
              have succ a > b, from ⟨this, H₂⟩,
              show succ a < b ∨ succ a = b ∨ succ a > b, from
                or.inr (or.inr this)))

    theorem not_eq_and_lt : ¬ (a = b ∧ a < b) :=
      assume H : a = b ∧ a < b,
      have a ≠ b, from H.right.right,
      absurd H.left this

    theorem not_eq_and_gt : ¬ (a = b ∧ a > b) :=
      assume H : a = b ∧ a > b,
      have a ≠ b, from H.right.right.symm,
      absurd H.left this

    theorem not_lt_and_gt : ¬ (a < b ∧ a > b) :=
      assume H : a < b ∧ a > b,
      have a ≤ b ∧ a > b, from ⟨H.left.left, H.right⟩,
      absurd this not_le_and_gt
  end trichotomy

  -- Some more order properties
  section order_equivalence
    variables {a b : N}

    theorem le_iff_not_gt : a ≤ b ↔ ¬ a > b :=
      iff.intro
        (assume (H₁ : a ≤ b) (H₂ : a > b),
          have a ≤ b ∧ a > b, from ⟨H₁, H₂⟩,
          absurd this not_le_and_gt)
        (assume H : ¬ a > b,
          show a ≤ b, from trichotomy.elim3
            (suppose a < b, this.left)
            (suppose a = b, ⟨0, this.symm ▸ add_zero_right.symm⟩)
            (suppose a > b, absurd this H))

    theorem gt_iff_not_le : a > b ↔ ¬ a ≤ b :=
      iff.intro
        (suppose a > b,
          have ¬ ¬ a > b, from not_not_intro this,
          show ¬ a ≤ b, from mt le_iff_not_gt.mp this)
        (suppose ¬ a ≤ b,
          have ¬ ¬ a > b, from mt le_iff_not_gt.mpr this,
          show a > b, from not_not_elim this)

    theorem ge_iff_not_lt : a ≥ b ↔ ¬ a < b :=
      @le_iff_not_gt b a

    theorem lt_iff_not_ge : a < b ↔ ¬ a ≥ b :=
      @gt_iff_not_le b a
  end order_equivalence

  -- Proposition 2.2.14: Strong principle of induction
  section strong_induction
    parameters (p : N → Prop) (n₀ : N)

    private def q (n : N) : Prop :=
      ∀ m : N, m ≥ n₀ ∧ m < n → p m

    theorem strong_induction (SI : ∀ {n : N}, n ≥ n₀ → q n → p n) :
        ∀ n : N, n ≥ n₀ → p n :=
      assume n : N,
      suffices H : n ≥ n₀ → q n, from
        suppose n ≥ n₀,
        show p n, from SI this (H this),
      show n ≥ n₀ → q n, from induction_on n
        (show 0 ≥ n₀ → q 0, from
          assume (H₁ : 0 ≥ n₀) (m : N) (H₂ : m ≥ n₀ ∧ m < 0),
          absurd H₂.right not_lt_zero)
        (assume (n : N) (IH : n ≥ n₀ → q n),
          show succ n ≥ n₀ → q (succ n), from
            assume (H₁ : succ n ≥ n₀) (m : N) (H₂ : m ≥ n₀ ∧ m < succ n),
            show p m, from by_cases
              (suppose n₀ = succ n,
                have m ≥ succ n, from this ▸ H₂.left,
                have m < succ n ∧ m ≥ succ n, from ⟨H₂.right, this⟩,
                absurd this not_lt_and_ge)
              (suppose n₀ ≠ succ n,
                have succ n > n₀, from ⟨H₁, this⟩,
                have n ≥ n₀, from lt_succ_iff_le.mp this,
                have Hqn : q n, from IH this,
                have Hpn : p n, from SI this Hqn,
                show p m, from by_cases
                  (suppose n = m, this ▸ Hpn)
                  (assume H : n ≠ m,
                    have m ≤ n, from lt_succ_iff_le.mp H₂.right,
                    have m < n, from ⟨this, H.symm⟩,
                    have m ≥ n₀ ∧ m < n, from ⟨H₂.left, this⟩,
                    show p m, from Hqn m this)))
  end strong_induction

  -- Exercise 2.2.6: Backward principle of induction
  example (n : N) (p : N → Prop) (BI : ∀ m : N, p (succ m) → p m) (Hp : p n) :
      ∀ m : N, m ≤ n → p m :=
    by_contradiction
      (suppose ¬ ∀ m : N, m ≤ n → p m,
        let ⟨m, (H₁ : ¬ (m ≤ n → p m))⟩ := dm_exists_not this in
        have m ≤ n ∧ ¬ p m, from not_imp_iff_and_not.mp H₁,
        let ⟨d, (H₂ : n = m + d)⟩ := this.left in
        have H₃ : ¬ p m, from this.right,
        have ¬ p (m + d), from induction_on d
          (show ¬ p (m + 0), by rw add_zero_right; exact H₃)
          (assume (d : N) (IH : ¬ p (m + d)),
            have p (succ (m + d)) → p (m + d), from BI (m + d),
            have ¬ p (succ (m + d)), from mt this IH,
            show ¬ p (m + succ d), by rw add_succ_right; exact this),
        have ¬ p n, from H₂.symm ▸ this,
        absurd Hp this)

  -- Definition 2.3.1: Multiplication of natural numbers
  def mul : N → N → N
    | 0 m := 0
    | (succ n) m := mul n m + m

  -- Type class instances
  instance : has_mul N := ⟨mul⟩
  instance : has_one N := ⟨succ 0⟩

  -- Part of Exercise 2.3.1
  lemma mul_zero_right {n : N} : n * 0 = 0 :=
    induction_on n
      (show zero * 0 = 0, from rfl) -- can't use 0 for some reason
      (assume (n : N) (IH : n * 0 = 0),
        show succ n * 0 = 0, from calc
          succ n * 0 = n * 0 + 0 : rfl
          ... = 0 + 0 : by rw IH
          ... = 0 : rfl)

  -- Part of Exercise 2.3.1
  lemma mul_succ_right {n m : N} : n * succ m = n * m + n :=
    induction_on n
      (show 0 * succ m = 0 * m + 0, from calc
        0 * succ m = 0 : rfl
        ... = 0 + 0 : rfl
        ... = 0 * m + 0 : rfl)
      (assume (n : N) (IH : n * succ m = n * m + n),
        show succ n * succ m = succ n * m + succ n, from calc
          succ n * succ m = n * succ m + succ m : rfl
          ... = n * m + n + succ m : by rw IH
          ... = n * m + (n + succ m) : add_assoc
          ... = n * m + (succ m + n) : by rw @add_comm (succ m) n
          ... = n * m + succ (m + n) : rfl
          ... = n * m + (m + succ n) : by rw @add_succ_right m n
          ... = n * m + m + succ n : add_assoc.symm
          ... = succ n * m + succ n : rfl)

  -- Lemma 2.3.2: Multiplication is commutative
  lemma mul_comm {n m : N} : n * m = m * n :=
    induction_on n
      (show 0 * m = m * 0, from calc
        0 * m = 0 : rfl
        ... = m * 0 : mul_zero_right.symm)
      (assume (n : N) (IH : n * m = m * n),
        show succ n * m = m * succ n, from calc
          succ n * m = n * m + m : rfl
          ... = m * n + m : by rw IH
          ... = m * succ n : mul_succ_right.symm)

  -- Lemma 2.3.3: Natural numbers have no zero divisors
  lemma mul_eq_zero {n m : N} : n * m = 0 ↔ n = 0 ∨ m = 0 :=
    iff.intro
      (assume H₁ : n * m = 0,
        show n = 0 ∨ m = 0, from by_cases
          (suppose n = 0, or.inl this)
          (suppose n ≠ 0,
            let ⟨n', (H₂ : succ n' = n)⟩ := pos_pred this in
            have 0 = n' * m + m, from calc
              0 = n * m : H₁.symm
              ... = succ n' * m : by rw H₂
              ... = n' * m + m : rfl,
            have m = 0, from (add_eq_zero this.symm).right,
            show n = 0 ∨ m = 0, from or.inr this))
      (suppose n = 0 ∨ m = 0,
        show n * m = 0, from this.elim
          (assume Hn : n = 0,
            have 0 * m = 0, from rfl,
            show n * m = 0, from Hn.symm ▸ this)
          (assume Hm : m = 0,
            have n * 0 = 0, from mul_zero_right,
            show n * m = 0, from Hm.symm ▸ this))

  -- Alternative form of Lemma 2.3.3
  lemma mul_pos {n m : N} : pos (n * m) ↔ pos n ∧ pos m :=
    iff.intro
      (suppose pos (n * m),
        have ¬ (n = 0 ∨ m = 0), from mt mul_eq_zero.mpr this,
        show pos n ∧ pos m, from dm_not_and_not this)
      (suppose pos n ∧ pos m,
        have ¬ (n = 0 ∨ m = 0), from dm_not_or this,
        show pos (n * m), from mt mul_eq_zero.mp this)

  -- Proposition 2.3.4: Distributive law
  section distributive_law
    variables {a b c : N}

    theorem left_distrib : a * (b + c) = a * b + a * c :=
      induction_on c
        (show a * (b + 0) = a * b + a * 0, from calc
          a * (b + 0) = a * b : by rw @add_zero_right b
          ... = a * b + 0 : add_zero_right.symm
          ... = a * b + a * 0 : by rw @mul_zero_right a)
        (assume (c : N) (IH : a * (b + c) = a * b + a * c),
          show a * (b + succ c) = a * b + a * succ c, from calc
            a * (b + succ c) = a * succ (b + c) : by rw @add_succ_right b c
            ... = a * (b + c) + a : mul_succ_right
            ... = a * b + a * c + a : by rw IH
            ... = a * b + (a * c + a) : add_assoc
            ... = a * b + a * succ c : by rw @mul_succ_right a c)

    theorem right_distrib : (b + c) * a = b * a + c * a :=
      calc
        (b + c) * a = a * (b + c) : mul_comm
        ... = a * b + a * c : left_distrib
        ... = b * a + a * c : by rw @mul_comm b a
        ... = b * a + c * a : by rw @mul_comm c a
  end distributive_law

  -- Proposition 2.3.5: Multiplication is associative
  theorem mul_assoc {a b c : N} : (a * b) * c = a * (b * c) :=
    induction_on a
      (show (0 * b) * c = 0 * (b * c), from calc
        (0 * b) * c = 0 * c : rfl
        ... = 0 : rfl
        ... = 0 * (b * c) : rfl)
      (assume (a : N) (IH : (a * b) * c = a * (b * c)),
        show (succ a * b) * c = succ a * (b * c), from calc
          (succ a * b) * c = (a * b + b) * c : rfl
          ... = (a * b) * c + b * c : right_distrib
          ... = a * (b * c) + b * c : by rw IH
          ... = succ a * (b * c) : rfl)

  -- Proposition 2.3.6: Multiplication preserves order
  theorem mul_lt_mul {a b c : N} (H₁ : a < b) (H₂ : pos c) : a * c < b * c :=
    let ⟨d, (Hd : b = a + d ∧ pos d)⟩ := lt_iff_pos.mp H₁ in
    have H₃ : b * c = a * c + d * c, from calc
      b * c = (a + d) * c : by rw Hd.left
      ... = a * c + d * c : right_distrib,
    have pos d ∧ pos c, from ⟨Hd.right, H₂⟩,
    have pos (d * c), from mul_pos.mpr this,
    show a * c < b * c, from lt_iff_pos.mpr ⟨d * c, ⟨H₃, this⟩⟩

  -- Corollary 2.3.7: Cancellation law
  theorem mul_cancel {a b c : N} (H₁ : a * c = b * c) (H₂ : pos c) : a = b :=
    trichotomy.elim3
      (suppose a < b,
        have a * c < b * c, from mul_lt_mul this H₂,
        absurd H₁ this.right)
      (suppose a = b, this)
      (suppose a > b,
        have a * c > b * c, from mul_lt_mul this H₂,
        absurd H₁ this.right.symm)

  -- Proposition 2.3.9: Euclidean algorithm
  theorem euclid_alg {n q : N} (H : pos q) : ∃ m r : N, r < q ∧ n = m * q + r :=
    have 0 ≤ q, from ⟨q, rfl⟩,
    have H₀ : 0 < q, from ⟨this, H.symm⟩,
    induction_on n
      (show ∃ m r : N, r < q ∧ 0 = m * q + r, from
        have 0 = 0 * q + 0, from calc
          0 = 0 * q : rfl
          ... = 0 * q + 0 : add_zero_right.symm,
        have 0 < q ∧ 0 = 0 * q + 0, from ⟨H₀, this⟩,
        ⟨0, ⟨0, this⟩⟩)
      (assume (n : N) (IH : ∃ m r : N, r < q ∧ n = m * q + r),
        let ⟨m, ⟨r, (IH : r < q ∧ n = m * q + r)⟩⟩ := IH in
        show ∃ m r : N, r < q ∧ succ n = m * q + r, from by_cases
          (suppose succ r = q,
            have succ n = succ m * q + 0, from calc
              succ n = succ (m * q + r) : by rw IH.right
              ... = m * q + succ r : add_succ_right.symm
              ... = m * q + q : by rw this
              ... = q * m + q : by rw @mul_comm q m
              ... = q * succ m : mul_succ_right.symm
              ... = succ m * q : mul_comm
              ... = succ m * q + 0 : add_zero_right.symm,
            have 0 < q ∧ succ n = succ m * q + 0, from ⟨H₀, this⟩,
            ⟨succ m, ⟨0, this⟩⟩)
          (suppose succ r ≠ q,
            have LT : succ r < q, from ⟨lt_iff_succ_le.mp IH.left, this⟩,
            have succ n = m * q + succ r, from calc
              succ n = succ (m * q + r) : by rw IH.right
              ... = m * q + succ r : add_succ_right.symm,
            have succ r < q ∧ succ n = m * q + succ r, from ⟨LT, this⟩,
            ⟨m, ⟨succ r, this⟩⟩))

  -- Definition 2.3.11: Exponentiation for natural numbers
  def pow : N → N → N
    | m 0 := 1
    | m (succ n) := pow m n * m

  -- Can't use ^ because has_pow_nat requires nat
  infixr ` ** `:80 := pow

  -- Exercise 2.3.4: Square of binomial
  example (a b : N) : (a + b)**2 = a**2 + 2 * a * b + b**2 :=
    have b * a + a * b = 2 * a * b, from calc
      b * a + a * b = a * b + a * b : by rw @mul_comm a b
      ... = 0 + a * b + a * b : rfl
      ... = a * b * 0 + a * b + a * b : by rw @mul_zero_right (a * b)
      ... = a * b * succ 0 + a * b : by rw @mul_succ_right (a * b) 0
      ... = a * b * succ (succ 0) : mul_succ_right.symm
      ... = a * b * 2 : rfl
      ... = 2 * (a * b) : mul_comm
      ... = 2 * a * b : mul_assoc.symm,
    show (a + b)**2 = a**2 + 2 * a * b + b**2, from calc
      (a + b)**2 = (a + b) * (a + b) : rfl
      ... = (a + b) * a + (a + b) * b : left_distrib
      ... = a * a + b * a + (a + b) * b : by rw @right_distrib a a b
      ... = a * a + b * a + (a * b + b * b) : by rw @right_distrib b a b
      ... = a * a + b * a + a * b + b * b :
        by rw @add_assoc (a * a + b * a) (a * b) (b * b)
      ... = a**2 + b * a + a * b + b * b : rfl
      ... = a**2 + b * a + a * b + b**2 : rfl
      ... = a**2 + (b * a + a * b) + b**2 :
        by rw @add_assoc (a**2) (b * a) (a * b)
      ... = a**2 + 2 * a * b + b**2 : by rw this
end N
