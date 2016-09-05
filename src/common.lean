-- Copyright 2016 Mitchell Kember. Subject to the MIT License.
-- Formalization of Analysis I: Common theorems

open classical

-- Returns a proposition which asserts that an object is of a certain type.
definition has_type : Π A : Type, A → Prop := λ A a, true

-- De Morgan's laws
section de_morgan
  premises {p q : Prop}

  theorem dm_not_or_not (H : ¬ (p ∧ q)) : ¬ p ∨ ¬ q :=
    by_cases
      (suppose p,
        have ¬ q, from
          suppose q,
          absurd (and.intro `p` `q`) H,
        show ¬ p ∨ ¬ q, from or.inr this)
      (suppose ¬ p,
        show ¬ p ∨ ¬ q, from or.inl this)

  theorem dm_not_and (H : ¬ p ∨ ¬ q) : ¬ (p ∧ q) :=
    suppose p ∧ q,
    show false, from or.elim H
      (suppose ¬ p, absurd (and.left `p ∧ q`) this)
      (suppose ¬ q, absurd (and.right `p ∧ q`) this)
        

  theorem dm_not_and_not (H : ¬ (p ∨ q)) : ¬ p ∧ ¬ q :=
    by_cases
      (suppose p,
        absurd (or.inl this) H)
      (suppose ¬ p,
        have ¬ q, from
          suppose q,
          absurd (or.inr this) H,
        show ¬ p ∧ ¬ q, from and.intro `¬ p` `¬ q`)

  theorem dm_not_or (H : ¬ p ∧ ¬ q) : ¬ (p ∨ q) :=
    suppose p ∨ q,
    show false, from or.elim this
      (suppose p, absurd this (and.left H))
      (suppose q, absurd this (and.right H))
end de_morgan

-- De Morgan's laws (general)
section de_morgan_general
  premises {A : Type} {p : A → Prop}

  theorem dm_exists_not (H : ¬ ∀ a : A, p a) : ∃ a : A, ¬ p a :=
    by_contradiction
      (assume H1 : ¬ ∃ a : A, ¬ p a,
        have ∀ a : A, p a, from
          take a,
          show p a, from by_contradiction
            (suppose ¬ p a,
              absurd (exists.intro a this) H1),
        absurd this H)

  theorem dm_not_forall (H : ∃ a : A, ¬ p a) : ¬ ∀ a : A, p a :=
    obtain (a : A) (H1 : ¬ p a), from H,
    suppose ∀ a : A, p a,
      absurd (this a) H1

  theorem dm_forall_not (H : ¬ ∃ a : A, p a) : ∀ a : A, ¬ p a :=
    take a,
    show ¬ p a, from
      suppose p a,
      absurd (exists.intro a this) H

  theorem dm_not_exists (H : ∀ a : A, ¬ p a) : ¬ ∃ a : A, p a :=
    suppose ∃ a : A, p a,
    obtain (a : A) (H1 : p a), from this,
    absurd H1 (H a)
end de_morgan_general
