-- Copyright 2016 Mitchell Kember. Subject to the MIT License.
-- Formalization of Analysis I: Common theorems

open classical

-- De Morgan's laws
section de_morgan
  variables {p q : Prop}

  theorem dm_not_or_not (H : ¬ (p ∧ q)) : ¬ p ∨ ¬ q :=
    by_cases
      (suppose p,
        have ¬ q, from
          suppose q,
          absurd (and.intro ‹p› ‹q›) H,
        show ¬ p ∨ ¬ q, from or.inr this)
      (suppose ¬ p,
        show ¬ p ∨ ¬ q, from or.inl this)

  theorem dm_not_and (H : ¬ p ∨ ¬ q) : ¬ (p ∧ q) :=
    assume Hpq : p ∧ q,
    show false, from or.elim H
      (suppose ¬ p, absurd Hpq.left this)
      (suppose ¬ q, absurd Hpq.right this)

  theorem dm_not_and_not (H : ¬ (p ∨ q)) : ¬ p ∧ ¬ q :=
    by_cases
      (suppose p,
        absurd (or.inl this) H)
      (suppose ¬ p,
        have ¬ q, from
          suppose q,
          absurd (or.inr this) H,
        show ¬ p ∧ ¬ q, from and.intro ‹¬ p› ‹¬ q›)

  theorem dm_not_or (H : ¬ p ∧ ¬ q) : ¬ (p ∨ q) :=
    suppose p ∨ q,
    show false, from or.elim this
      (suppose p, absurd this H.left)
      (suppose q, absurd this H.right)
end de_morgan

-- De Morgan's laws (general)
section de_morgan_general
  variables {A : Type} {p : A → Prop}

  theorem dm_exists_not (H : ¬ ∀ a : A, p a) : ∃ a : A, ¬ p a :=
    by_contradiction
      (assume H₁ : ¬ ∃ a : A, ¬ p a,
        have ∀ a : A, p a, from
          take a,
          show p a, from by_contradiction
            (suppose ¬ p a,
              absurd (exists.intro a this) H₁),
        absurd this H)

  theorem dm_not_forall (H : ∃ a : A, ¬ p a) : ¬ ∀ a : A, p a :=
    let ⟨a, H₁⟩ := H in
    suppose ∀ a : A, p a,
    absurd (this a) H₁

  theorem dm_forall_not (H : ¬ ∃ a : A, p a) : ∀ a : A, ¬ p a :=
    take a,
    show ¬ p a, from
      suppose p a,
      absurd (exists.intro a this) H

  theorem dm_not_exists (H : ∀ a : A, ¬ p a) : ¬ ∃ a : A, p a :=
    suppose ∃ a : A, p a,
    let ⟨a, H₁⟩ := this in
    absurd H₁ (H a)
end de_morgan_general
