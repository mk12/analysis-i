-- Copyright 2016 Mitchell Kember. Subject to the MIT License.
-- Formalization of Analysis I: Common theorems

open classical (by_cases by_contradiction)

-- Classical double negation elimination
theorem not_not_elim {p : Prop} (H : ¬ ¬ p) : p :=
  by_cases
    (assume Hp : p, Hp)
    (assume Hnp : ¬ p, absurd Hnp H)

-- De Morgan's laws
section de_morgan
  variables {p q : Prop}

  theorem dm_not_or_not (H : ¬ (p ∧ q)) : ¬ p ∨ ¬ q :=
    by_cases
      (assume Hp : p,
        have ¬ q, from
          assume Hq : q,
          have p ∧ q, from ⟨Hp, Hq⟩,
          absurd this H,
        show ¬ p ∨ ¬ q, from or.inr this)
      (suppose ¬ p, or.inl this)

  theorem dm_not_and (H : ¬ p ∨ ¬ q) : ¬ (p ∧ q) :=
    assume Hpq : p ∧ q,
    H.elim
      (suppose ¬ p, absurd Hpq.left this)
      (suppose ¬ q, absurd Hpq.right this)

  theorem dm_not_and_not (H : ¬ (p ∨ q)) : ¬ p ∧ ¬ q :=
    by_cases
      (suppose p, absurd (or.inl this) H)
      (assume Hnp : ¬ p,
        have Hnq : ¬ q, from
          suppose q,
          absurd (or.inr this) H,
        show ¬ p ∧ ¬ q, from ⟨Hnp, Hnq⟩)

  theorem dm_not_or (H : ¬ p ∧ ¬ q) : ¬ (p ∨ q) :=
    suppose p ∨ q,
    this.elim
      (suppose p, absurd this H.left)
      (suppose q, absurd this H.right)
end de_morgan

-- De Morgan's laws (general)
section de_morgan_general
  variables {A : Type} {p : A → Prop}

  theorem dm_exists_not (H : ¬ ∀ a : A, p a) : ∃ a : A, ¬ p a :=
    by_contradiction
      (assume H₁ : ¬ ∃ a : A, ¬ p a,
        suffices ∀ a : A, p a, from absurd this H,
        assume a : A,
        show p a, from by_contradiction
          (suppose ¬ p a,
            have ∃ a : A, ¬ p a, from ⟨a, this⟩,
            absurd this H₁))

  theorem dm_not_forall (H : ∃ a : A, ¬ p a) : ¬ ∀ a : A, p a :=
    let ⟨a, (H₁ : ¬ p a)⟩ := H in
    suppose ∀ a : A, p a,
    absurd (this a) H₁

  theorem dm_forall_not (H : ¬ ∃ a : A, p a) : ∀ a : A, ¬ p a :=
    assume (a : A) (H₁ : p a),
    have ∃ a : A, p a, from ⟨a, H₁⟩,
    absurd this H

  theorem dm_not_exists (H : ∀ a : A, ¬ p a) : ¬ ∃ a : A, p a :=
    suppose ∃ a : A, p a,
    let ⟨a, (H₁ : p a)⟩ := this in
    absurd H₁ (H a)
end de_morgan_general

-- Implication helpers
section implies
  variables {a b : Prop}

  theorem imp_iff_not_or : a → b ↔ ¬ a ∨ b :=
    iff.intro
      (assume H : a → b,
        show ¬ a ∨ b, from by_cases
          (suppose a, or.inr (H this))
          (suppose ¬ a, or.inl this))
      (assume (H : ¬ a ∨ b) (Ha : a), H.elim
        (suppose ¬ a, absurd Ha this)
        (suppose b, this))

  theorem not_imp_iff_and_not : ¬ (a → b) ↔ a ∧ ¬ b :=
    iff.intro
      (suppose ¬ (a → b),
        have ¬ (¬ a ∨ b), from mt imp_iff_not_or.mpr this,
        have ¬ ¬ a ∧ ¬ b, from dm_not_and_not this,
        show a ∧ ¬ b, from ⟨not_not_elim this.left, this.right⟩)
      (assume H : a ∧ ¬ b,
        suppose a → b,
        absurd (this H.left) H.right)
end implies

-- Disjunction helpers
namespace or
  variables {a b c d : Prop}
  
  theorem elim3 (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
    H.elim Ha (suppose b ∨ c, this.elim Hb Hc)
end or
