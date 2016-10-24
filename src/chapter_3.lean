-- Copyright 2016 Mitchell Kember. Subject to the MIT ficense.
-- Formalization of Analysis I: Chapter 3

import .common .chapter_2

open classical eq.ops sigma.ops

-- A set is defined as a membership predicate
definition set (X : Type) : Type := X → Prop

namespace set
  -- Basic definitions
  section basic
    variable {X : Type}

    definition mem (x : X) (A : set X) : Prop := A x
    definition empty : set X := λ x, false

    infix ` ∈ ` := mem
    notation a ` ∉ ` s := ¬ mem a s
    notation `∅` := empty
  end basic

  -- Universe class of objects
  universe Universe
  constant Object : Type.{Universe}
  abbreviation Set := set Object

  -- Axiom 3.1: Sets are objects
  axiom A1 : ∀ (A : Set) (B : set Set), has_type Prop (A ∈ B)

  -- Definition 3.1.4: Equality of sets
  axiom set_eq {A B : Set} : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B

  -- Introduction and elimination rules
  section intro_elim
    variables {A B : Set}

    proposition set_eq_intro
        (H₁ : ∀ x, x ∈ A → x ∈ B) (H₂ : ∀ x, x ∈ B → x ∈ A) : A = B :=
      have ∀ x, x ∈ A ↔ x ∈ B, from
        take x,
        iff.intro (H₁ x) (H₂ x),
      show A = B, from iff.mpr set_eq this

    proposition set_eq_elim : A = B → ∀ x, x ∈ A ↔ x ∈ B :=
      iff.mp set_eq
  end intro_elim

  -- Axiom 3.2: Empty set
  theorem not_in_empty {x : Object} : x ∉ ∅ := id

  -- Convenient way of demonstrating emptiness
  proposition no_elements {A : Set} (H : ∀ x, x ∉ A) : A = ∅ :=
    set_eq_intro
      (take x, suppose x ∈ A, absurd this (H x))
      (take x, suppose x ∈ ∅, absurd this not_in_empty)

  -- Lemma 3.1.6: Single choice
  lemma single_choice {A : Set} (H : A ≠ ∅) : ∃ x, x ∈ A :=
    by_contradiction
      (suppose ¬ ∃ x, x ∈ A,
        have ∀ x, x ∉ A, from dm_forall_not this,
        have A = ∅, from no_elements this,
        absurd this H)

  -- Axiom 3.3: Singleton sets
  definition singleton (x) : Set := λ y, x = y

  -- Axiom 3.4: Pairwise union
  definition union (A B : Set) : Set := λ x, x ∈ A ∨ x ∈ B
  infix ` ∪ ` := union

  -- Lemma 3.1.12
  section union_properties
    variables {A B C : Set}

    lemma union_comm : A ∪ B = B ∪ A :=
      set_eq_intro
        (take x, suppose x ∈ A ∪ B, or.swap this)
        (take x, suppose x ∈ B ∪ A, or.swap this)

    lemma union_assoc : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
      set_eq_intro
        (take x, suppose x ∈ (A ∪ B) ∪ C, iff.mp or.assoc this)
        (take x, suppose x ∈ A ∪ (B ∪ C), iff.mpr or.assoc this)

    lemma union_idemp : A ∪ A = A :=
      set_eq_intro
        (take x, suppose x ∈ A ∪ A, or.elim this id id)
        (take x, suppose x ∈ A, or.inl this)

    lemma union_empty : A ∪ ∅ = A :=
      set_eq_intro
        (take x, suppose x ∈ A ∪ ∅, or.elim this id false.elim)
        (take x, suppose x ∈ A, or.inl this)
  end union_properties

  -- Definition 3.1.14: Subsets
  definition subset (A B : Set) : Prop := ∀ {{x}}, x ∈ A → x ∈ B
  infix ` ⊆ ` := subset
  definition proper_subset (A B : Set) : Prop := A ⊆ B ∧ A ≠ B
  infix ` ⊂ `:50 := proper_subset

  -- Proposition 3.1.17: Sets are partially ordered by set inclusion
  section subset_properties
    variables {A B C : Set}

    proposition subset_of_eq (H : A = B) : A ⊆ B :=
      take a,
      suppose a ∈ A,
      show a ∈ B, from H ▸ this

    proposition subset_antisymm (H₁ : A ⊆ B) (H₂ : B ⊆ A) : A = B :=
      set_eq_intro H₁ H₂

    proposition subset_trans (H₁ : A ⊆ B) (H₂ : B ⊆ C) : A ⊆ C :=
      take a,
      suppose a ∈ A,
      have a ∈ B, from H₁ this,
      show a ∈ C, from H₂ this

    proposition psubset_trans (H₁ : A ⊂ B) (H₂ : B ⊂ C) : A ⊂ C :=
      have H₁' : A ⊆ B, from and.left H₁,
      have H₂' : B ⊆ C, from and.left H₂,
      have A ⊆ C, from subset_trans H₁' H₂',
      have A ≠ C, from
        suppose A = C,
        have H₃ : C ⊆ A, from subset_of_eq this⁻¹,
        have A = B, from set_eq_intro
          (take x, suppose x ∈ A, H₁' this)
          (take x, suppose x ∈ B, H₃ (H₂' this)),
        absurd this (and.right H₁),
      show A ⊂ C, from and.intro `A ⊆ C` `A ≠ C`
  end subset_properties

  -- Axiom 3.5: Axiom of specification
  definition specify (A : Set) (P : Object → Prop) : Set := λ x, x ∈ A ∧ P x
  notation `{` binder ` ∈ ` A ` : ` r:(scoped:1 P, specify A P) `}` := r

  -- Definition 3.1.22: Intersections
  definition inter (A B : Set) : Set := λ x, x ∈ A ∧ x ∈ B
  infix ` ∩ ` := inter

  -- Definition 3.1.26: Difference sets
  definition diff (A B : Set) : Set := λ x, x ∈ A ∧ x ∉ B
  infix ` \ `:70 := diff

  -- Proposition 3.1.27: Sets form a boolean algebra
  section boolean_algebra
    variables {A B C X : Set}
    premises (HA : A ⊆ X) (HB : B ⊆ X) (HC : C ⊆ X)

    -- Minimal element

    example : A ∪ ∅ = A := union_empty

    proposition inter_empty : A ∩ ∅ = ∅ :=
      no_elements
        (take x, suppose x ∈ A ∩ ∅, absurd (and.right this) not_in_empty)

    -- Maximal element

    proposition union_super : A ∪ X = X :=
      set_eq_intro
        (take x, suppose x ∈ A ∪ X, or.elim this !HA id)
        (take x, suppose x ∈ X, or.inr this)

    proposition inter_super : A ∩ X = A :=
      set_eq_intro
        (take x, suppose x ∈ A ∩ X, and.left this)
        (take x, suppose x ∈ A, and.intro this (HA this))

    -- Identity

    example : A ∪ A = A := union_idemp

    proposition inter_idemp : A ∩ A = A :=
      set_eq_intro
        (take x, suppose x ∈ A ∩ A, and.left this)
        (take x, suppose x ∈ A, and.intro this this)

    -- Commutativity

    example : A ∪ B = B ∪ A := union_comm

    proposition inter_comm : A ∩ B = B ∩ A :=
      set_eq_intro
        (take x, suppose x ∈ A ∩ B, and.swap this)
        (take x, suppose x ∈ B ∩ A, and.swap this)

    -- Associativity

    example : (A ∪ B) ∪ C = A ∪ (B ∪ C) := union_assoc

    proposition inter_assoc : (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
      set_eq_intro
        (take x, suppose x ∈ (A ∩ B) ∩ C, iff.mp and.assoc this)
        (take x, suppose x ∈ A ∩ (B ∩ C), iff.mpr and.assoc this)

    -- Distributivity

    proposition union_distrib : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
      set_eq_intro
        (take x,
          suppose x ∈ A ∪ (B ∩ C),
          show x ∈ (A ∪ B) ∩ (A ∪ C), from or.elim this
            (suppose x ∈ A, and.intro (or.inl this) (or.inl this))
            (suppose x ∈ B ∩ C,
              have H₁ : x ∈ (A ∪ B), from or.inr (and.left this),
              have H₂ : x ∈ (A ∪ C), from or.inr (and.right this),
              show x ∈ (A ∪ B) ∩ (A ∪ C), from and.intro H₁ H₂))
        (take x,
          suppose x ∈ (A ∪ B) ∩ (A ∪ C),
          have H₁ : x ∈ A ∪ B, from and.left this,
          have H₂ : x ∈ A ∪ C, from and.right this,
          show x ∈ A ∪ (B ∩ C), from by_cases
            (suppose x ∈ A, or.inl this)
            (suppose x ∉ A,
              have x ∈ B, from or.resolve_left H₁ `x ∉ A`,
              have x ∈ C, from or.resolve_left H₂ `x ∉ A`,
              have x ∈ B ∩ C, from and.intro `x ∈ B` `x ∈ C`,
              show x ∈ A ∪ (B ∩ C), from or.inr this))

    proposition inter_distrib : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
      set_eq_intro
        (take x,
          suppose x ∈ A ∩ (B ∪ C),
          have H₁ : x ∈ A, from and.left this,
          have H₂ : x ∈ B ∪ C, from and.right this,
          show x ∈ (A ∩ B) ∪ (A ∩ C), from or.elim H₂
            (suppose x ∈ B, or.inl (and.intro H₁ this))
            (suppose x ∈ C, or.inr (and.intro H₁ this)))
        (take x,
          suppose x ∈ (A ∩ B) ∪ (A ∩ C),
          show x ∈ A ∩ (B ∪ C), from or.elim this
            (suppose x ∈ A ∩ B,
              have H₁ : x ∈ A, from and.left this,
              have H₂ : x ∈ B, from and.right this,
              show x ∈ A ∩ (B ∪ C), from and.intro H₁ (or.inl H₂))
            (suppose x ∈ A ∩ C,
              have H₁ : x ∈ A, from and.left this,
              have H₂ : x ∈ C, from and.right this,
              show x ∈ A ∩ (B ∪ C), from and.intro H₁ (or.inr H₂)))

    -- Partition

    proposition union_partition : A ∪ (X \ A) = X :=
      set_eq_intro
        (take x,
          suppose x ∈ A ∪ (X \ A),
          show x ∈ X, from or.elim this !HA and.left)
        (take x,
          suppose x ∈ X,
          show x ∈ A ∪ (X \ A), from by_cases
            (suppose x ∈ A, or.inl this)
            (suppose x ∉ A, or.inr (and.intro `x ∈ X` this)))

    proposition inter_partition : A ∩ (X \ A) = ∅ :=
      no_elements
        (take x,
          assume H : x ∈ A ∩ (X \ A),
          have x ∈ A, from and.left H,
          have x ∉ A, from and.right (and.right H),
          absurd `x ∈ A` `x ∉ A`)

    -- De Morgan laws

    proposition union_dm : X \ (A ∪ B) = (X \ A) ∩ (X \ B) :=
      set_eq_intro
        (take x,
          suppose x ∈ X \ (A ∪ B),
          have H₁ : x ∈ X, from and.left this,
          have x ∉ A ∪ B, from and.right this,
          have H₂ : x ∉ A ∧ x ∉ B, from dm_not_and_not this,
          have H₃ : x ∈ X \ A, from and.intro H₁ (and.left H₂),
          have H₄ : x ∈ X \ B, from and.intro H₁ (and.right H₂),
          show x ∈ (X \ A) ∩ (X \ B), from and.intro H₃ H₄)
        (take x,
          suppose x ∈ (X \ A) ∩ (X \ B),
          have H₁ : x ∈ X, from and.left (and.left this),
          have H₂ : x ∉ A, from and.right (and.left this),
          have H₃ : x ∉ B, from and.right (and.right this),
          have x ∉ A ∪ B, from dm_not_or (and.intro H₂ H₃),
          show x ∈ X \ (A ∪ B), from and.intro H₁ this)

    proposition inter_dm : X \ (A ∩ B) = (X \ A) ∪ (X \ B) :=
      set_eq_intro
        (take x,
          assume H : x ∈ X \ (A ∩ B),
          have x ∈ X, from and.left H,
          have x ∉ A ∨ x ∉ B, from dm_not_or_not (and.right H),
          show x ∈ (X \ A) ∪ (X \ B), from or.elim this
            (suppose x ∉ A, or.inl (and.intro `x ∈ X` this))
            (suppose x ∉ B, or.inr (and.intro `x ∈ X` this)))
        (take x,
          suppose x ∈ (X \ A) ∪ (X \ B),
          show x ∈ X \ (A ∩ B), from or.elim this
            (suppose x ∈ X \ A,
              have H₁ : x ∈ X, from and.left this,
              have x ∉ A, from and.right this,
              have x ∉ A ∨ x ∉ B, from or.inl this,
              have H₂ : x ∉ A ∩ B, from dm_not_and this,
              show x ∈ X \ (A ∩ B), from and.intro H₁ H₂)
            (suppose x ∈ X \ B,
              have H₁ : x ∈ X, from and.left this,
              have x ∉ B, from and.right this,
              have x ∉ A ∨ x ∉ B, from or.inr this,
              have H₂ : x ∉ A ∩ B, from dm_not_and this,
              show x ∈ X \ (A ∩ B), from and.intro H₁ H₂))
  end boolean_algebra

  -- Axiom 3.6: Replacement
  definition replace (A : Set) (P : Object → Object → Prop) : Set :=
    λ y, ∃ x, x ∈ A ∧ P x y

  -- More convenient form of Axiom 3.6
  definition map (A : Set) (f : Object → Object) : Set :=
    replace A (λ x y, y = f x)

  -- Axiom 3.7: Infinity
  definition infinity : set N := λ x, true

  -- Exercise 3.1.1
  section equivalence
    variables {A B C : Set}

    -- Reflexive
    example : A = A :=
      let f := take x, id in set_eq_intro f f

    -- Symmetric
    example (H : A = B) : B = A :=
      have ∀ x, x ∈ B ↔ x ∈ A, from
        take x,
        have x ∈ A ↔ x ∈ B, from set_eq_elim H x,
        show x ∈ B ↔ x ∈ A, from iff.symm this,
      show B = A, from iff.mpr set_eq this

    -- Transitive
    example (H₁ : A = B) (H₂ : B = C) : A = C :=
      have H₁' : ∀ {x}, x ∈ A ↔ x ∈ B, from set_eq_elim H₁,
      have H₂' : ∀ {x}, x ∈ B ↔ x ∈ C, from set_eq_elim H₂,
      show A = C, from set_eq_intro
        (take x, suppose x ∈ A, iff.mp H₂' (iff.mp H₁' this))
        (take x, suppose x ∈ C, iff.mpr H₁' (iff.mpr H₂' this))
  end equivalence

  -- Exercise 3.1.5
  section
    variables {A B : Set}

    -- (1) → (2)
    example (H : A ⊆ B) : A ∪ B = B :=
      set_eq_intro
        (take x, suppose x ∈ A ∪ B, or.elim this !H id)
        (take x, suppose x ∈ B, or.inr this)

    -- (2) → (3)
    example (H : A ∪ B = B) : A ∩ B = A :=
      have H' : A ∪ B ⊆ B, from subset_of_eq H,
      set_eq_intro
        (take x, suppose x ∈ A ∩ B, and.left this)
        (take x, suppose x ∈ A, and.intro this (H' (or.inl this)))

    -- (3) → (1)
    example (H : A ∩ B = A) : A ⊆ B :=
      have H' : A ⊆ A ∩ B, from subset_of_eq H⁻¹,
      take x,
      suppose x ∈ A,
      have x ∈ A ∩ B, from H' this,
      show x ∈ B, from and.right this
  end

  -- Exercise 3.1.7
  section
    variables {A B C : Set}

    example : A ∩ B ⊆ A :=
      take x,
      suppose x ∈ A ∩ B,
      show x ∈ A, from and.left this

    example : A ∩ B ⊆ B :=
      take x,
      suppose x ∈ A ∩ B,
      show x ∈ B, from and.right this

    example : C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B :=
      iff.intro
        (suppose C ⊆ A ∧ C ⊆ B,
          have H₁ : C ⊆ A, from and.left this,
          have H₂ : C ⊆ B, from and.right this,
          show C ⊆ A ∩ B, from
            take x,
            suppose x ∈ C,
            show x ∈ A ∧ x ∈ B, from and.intro (H₁ this) (H₂ this))
        (suppose H : C ⊆ A ∩ B,
          have C ⊆ A, from
            take x,
            suppose x ∈ C,
            have x ∈ A ∩ B, from H this,
            show x ∈ A, from and.left this,
          have C ⊆ B, from
            take x,
            suppose x ∈ C,
            have x ∈ A ∩ B, from H this,
            show x ∈ B, from and.right this,
          show C ⊆ A ∧ C ⊆ B, from and.intro `C ⊆ A` `C ⊆ B`)

    example : A ⊆ A ∪ B :=
      take x,
      suppose x ∈ A,
      show x ∈ A ∪ B, from or.inl this

    example : B ⊆ A ∪ B :=
      take x,
      suppose x ∈ B,
      show x ∈ A ∪ B, from or.inr this

    example : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C :=
      iff.intro
        (assume H : A ⊆ C ∧ B ⊆ C,
          show A ∪ B ⊆ C, from
            take x,
            suppose x ∈ A ∪ B,
            show x ∈ C, from or.elim this
              (suppose x ∈ A, and.left H x this)
              (suppose x ∈ B, and.right H x this))
        (assume H : A ∪ B ⊆ C,
          have A ⊆ C, from
            take x,
            suppose x ∈ A,
            have x ∈ A ∪ B, from or.inl this,
            show x ∈ C, from H this,
          have B ⊆ C, from
            take x,
            suppose x ∈ B,
            have x ∈ A ∪ B, from or.inr this,
            show x ∈ C, from H this,
          show A ⊆ C ∧ B ⊆ C, from and.intro `A ⊆ C` `B ⊆ C`)
  end

  -- Exercise 3.1.8
  section absorption
    variables {A B : Set}

    example : A ∩ (A ∪ B) = A :=
      set_eq_intro
        (take x, suppose x ∈ A ∩ (A ∪ B), and.left this)
        (take x, suppose x ∈ A, and.intro this (or.inl this))

    example : A ∪ (A ∩ B) = A :=
      set_eq_intro
        (take x, suppose x ∈ A ∪ (A ∩ B), or.elim this id and.left)
        (take x, suppose x ∈ A, or.inl this)
  end absorption

  -- Exercise 3.1.9
  section
    variables {A B X : Set}
    premises (H₁ : A ∪ B = X) (H₂ : A ∩ B = ∅)

    private proposition inverse_one : A = X \ B :=
      set_eq_intro
        (take x,
          suppose x ∈ A,
          have x ∈ X, from H₁ ▸ or.inl this,
          have x ∉ B, from
            suppose x ∈ B,
            have x ∈ A ∩ B, from and.intro `x ∈ A` `x ∈ B`,
            have x ∈ ∅, from H₂ ▸ this,
            absurd this not_in_empty,
          show x ∈ X \ B, from and.intro `x ∈ X` `x ∉ B`)
        (take x,
          suppose x ∈ X \ B,
          have H₃ : x ∈ A ∪ B, from H₁⁻¹ ▸ and.left this,
          have H₄ : x ∉ B, from and.right this,
          show x ∈ A, from by_contradiction
            (suppose x ∉ A,
              have x ∉ A ∧ x ∉ B, from and.intro this H₄,
              have x ∉ A ∪ B, from dm_not_or this,
              absurd H₃ this))

    private proposition inverse_two : B = X \ A :=
      inverse_one (union_comm ▸ H₁) (inter_comm ▸ H₂)
  end

  -- Exercise 3.1.10
  section
    variables {A B : Set}

    example : (A \ B) ∩ (B \ A) = ∅ :=
      no_elements
        (take x,
          assume H : x ∈ (A \ B) ∩ (B \ A),
          have x ∈ A, from and.left (and.left H),
          have x ∉ A, from and.right (and.right H),
          absurd `x ∈ A` `x ∉ A`)

    example : (A \ B) ∩ (A ∩ B) = ∅ :=
      no_elements
        (take x,
          assume H : x ∈ (A \ B) ∩ (A ∩ B),
          have x ∈ B, from and.right (and.right H),
          have x ∉ B, from and.right (and.left H),
          absurd `x ∈ B` `x ∉ B`)

    example : (B \ A) ∩ (A ∩ B) = ∅ :=
      no_elements
        (take x,
          assume H : x ∈ (B \ A) ∩ (A ∩ B),
          have x ∈ A, from and.left (and.right H),
          have x ∉ A, from and.right (and.left H),
          absurd `x ∈ A` `x ∉ A`)

    example : (A \ B) ∪ (A ∩ B) ∪ (B \ A) = A ∪ B :=
      set_eq_intro
        (take x,
          suppose x ∈ (A \ B) ∪ (A ∩ B) ∪ (B \ A),
          show x ∈ A ∪ B, from or.elim this
            (suppose x ∈ (A \ B) ∪ (A ∩ B), or.elim this
              (suppose x ∈ A \ B, or.inl (and.left this))
              (suppose x ∈ A ∩ B, or.inl (and.left this)))
            (suppose x ∈ B \ A, or.inr (and.left this)))
        (take x,
          suppose x ∈ A ∪ B,
          show x ∈ (A \ B) ∪ (A ∩ B) ∪ (B \ A), from or.elim this
            (suppose x ∈ A, by_cases
              (suppose x ∈ B, or.inl (or.inr (and.intro `x ∈ A` `x ∈ B`)))
              (suppose x ∉ B, or.inl (or.inl (and.intro `x ∈ A` `x ∉ B`))))
            (suppose x ∈ B, by_cases
              (suppose x ∈ A, or.inl (or.inr (and.intro `x ∈ A` `x ∈ B`)))
              (suppose x ∉ A, or.inr (and.intro `x ∈ B` `x ∉ A`))))
  end

  -- Convert Set to Type using dependent pairs
  definition Mem (X : Set) : Type := Σ x, x ∈ X

  -- Single choice for Mem
  noncomputable definition single_choice_mem {X : Set} (H : X ≠ ∅) : Mem X :=
    have ∃ a, a ∈ X, from single_choice H,
    sigma.mk (some this) (some_spec this)

  -- Definition 3.3.1: Functions
  definition Fun (X Y : Set) : Type := Mem X → Mem Y
  infixr ` => `:25 := Fun

  -- Definition 3.3.7: Equality of functions
  axiom fun_eq {X Y : Set} {f g : X => Y} : f = g ↔ ∀ x : Mem X, f x = g x

  -- Introduction and elimination rules
  section intro_elim
    variables {X Y : Set} {f g : X => Y}

    proposition fun_eq_intro : (∀ x : Mem X, f x = g x) → f = g :=
      iff.mpr fun_eq

    proposition fun_eq_elim : f = g → ∀ x : Mem X, f x = g x :=
      iff.mp fun_eq
  end intro_elim

  -- Definition 3.3.10: Composition
  definition comp {X Y Z : Set} (g : Y => Z) (f : X => Y) : X => Z :=
    λ x : Mem X, g (f x)
  infixr ` ∘ ` := comp

  -- Lemma 3.3.12: Composition is associative
  lemma comp_assoc {X Y Z W : Set} (f : Z => W) (g : Y => Z) (h : X => Y) :
      f ∘ (g ∘ h) = (f ∘ g) ∘ h :=
    fun_eq_intro
      (take x : Mem X,
        show (f ∘ (g ∘ h)) x = ((f ∘ g) ∘ h) x, from calc
          (f ∘ (g ∘ h)) x = f ((g ∘ h) x) : rfl
          ... = f (g (h x)) : rfl
          ... = (f ∘ g) (h x) : rfl
          ... = ((f ∘ g) ∘ h) x : rfl)

  -- Definition 3.3.14: One-to-one functions
  definition injective {X Y : Set} (f : X => Y) : Prop :=
    ∀ {{x x' : Mem X}}, f x = f x' → x = x'

  -- Definition 3.3.17: Onto functions
  definition surjective {X Y : Set} (f : X => Y) : Prop :=
    ∀ y : Mem Y, ∃ x : Mem X, f x = y

  -- Definition 3.3.20: Bijective functions
  definition bijective {X Y : Set} (f : X => Y) : Prop :=
    injective f ∧ surjective f

  -- Inverse functions
  section inverse
    variables {X Y : Set}

    definition left_inverse (f : X => Y) (g : Y => X) : Prop :=
      g ∘ f = id

    definition inverse (f : X => Y) (g : Y => X) : Prop :=
      ∀ (x : Mem X) (y : Mem Y), f x = y ↔ g y = x
    infix ` ~~ `:50 := inverse

    definition invertible (f : X => Y) : Prop :=
      ∃ g : Y => X, f ~~ g
  end inverse

  -- Properties of inverse functions
  section inverse_properties
    variables {X Y : Set} {f : X => Y} {g : Y => X}

    proposition inverse_symm (H : f ~~ g) : g ~~ f :=
      take (y : Mem Y) (x : Mem X),
      show g y = x ↔ f x = y, from iff.symm (H x y)

    proposition inverse_iff_both :
        f ~~ g ↔ left_inverse f g ∧ left_inverse g f :=
      iff.intro
        (assume H : f ~~ g,
          have HL : g ∘ f = id, from fun_eq_intro
            (take x : Mem X, iff.mp (H x (f x)) rfl),
          have HR : f ∘ g = id, from fun_eq_intro
            (take y : Mem Y, iff.mpr (H (g y) y) rfl),
          show left_inverse f g ∧ left_inverse g f, from and.intro HL HR)
        (suppose H : left_inverse f g ∧ left_inverse g f,
          take (x : Mem X) (y : Mem Y),
          show f x = y ↔ g y = x, from iff.intro
            (suppose f x = y,
              show g y = x, from calc
                g y = g (f x) : {this⁻¹}
                ... = x : fun_eq_elim (and.left H) x)
            (suppose g y = x,
              show f x = y, from calc
                f x = f (g y) : {this⁻¹}
                ... = y : fun_eq_elim (and.right H) y))
  end inverse_properties

  -- More properties of inverse functions
  section more_inverse_properties
    variables {X Y : Set} {f : X => Y}

    private lemma unique_of_injective {y : Mem Y} (Hi : injective f)
        (Hx : ∃ x : Mem X, f x = y) : ∃! x : Mem X, f x = y :=
      have ∀ x x' : Mem X, f x = y → f x' = y → x = x', from
        take x x' : Mem X,
        assume (H : f x = y) (H' : f x' = y),
        have f x = f x', from H'⁻¹ ▸ H,
        show x = x', from Hi this,
      show ∃! x : Mem X, f x = y, from
        exists_unique_of_exists_of_unique Hx this

    proposition left_of_nonempty_of_injective (Hn : X ≠ ∅) (Hi : injective f) :
        ∃ g : Y => X, left_inverse f g :=
      let g (y : Mem Y) : Mem X :=
        if H : ∃! x : Mem X, f x = y
          then the H
          else single_choice_mem Hn
      in
      have g ∘ f = id, from fun_eq_intro
        (take a : Mem X,
          have ∃ x : Mem X, f x = f a, from exists.intro a rfl,
          have H : ∃! x : Mem X, f x = f a, from unique_of_injective Hi this,
          show g (f a) = a, from calc
            g (f a) = the H : dif_pos H
            ... = a : eq_the H rfl),
      show ∃ g : Y => X, left_inverse f g, from exists.intro g this

    proposition injective_of_left (H : ∃ g : Y => X, left_inverse f g) :
        injective f :=
      obtain (g : Y => X) (Hg : g ∘ f = id), from H,
      show injective f, from
        take x x' : Mem X,
        suppose f x = f x',
        show x = x', from calc
          x = g (f x) : fun_eq_elim Hg x
          ... = g (f x') : {this}
          ... = x' : fun_eq_elim Hg x'

    proposition right_of_surjective (Hs : surjective f) :
        ∃ g : Y => X, left_inverse g f :=
      let g (y : Mem Y) : Mem X := some (Hs y)
      in
      have f ∘ g = id, from fun_eq_intro
        (take y : Mem Y,
          show f (g y) = y, from calc
          f (g y) = f (some (Hs y)) : rfl
          ... = y : some_spec (Hs y)),
      show ∃ g : Y => X, left_inverse g f, from exists.intro g this

    proposition surjective_of_right (H : ∃ g : Y => X, left_inverse g f) :
        surjective f :=
      obtain (g : Y => X) (Hg : f ∘ g = id), from H,
      show surjective f, from
        take y : Mem Y,
        have f (g y) = y, from fun_eq_elim Hg y,
        show ∃ x : Mem X, f x = y, from exists.intro (g y) this

    private lemma empty_invertible (Hn : X = ∅) (Hs : surjective f) :
        invertible f :=
      let g (y : Mem Y) : Mem X := some (Hs y)
      in
      have f ~~ g, from
        take (x : Mem X) (y : Mem Y),
        show f x = y ↔ g y = x, from absurd (Hn ▸ x.2) not_in_empty,
      show invertible f, from exists.intro g this

    private lemma left_eq_right {g g' : Y => X} (Hf : bijective f)
        (HL : left_inverse f g) (HR : left_inverse g' f) : g = g' :=
      have Hi : injective f, from and.left Hf,
      have Hs : surjective f, from and.right Hf,
      show g = g', from fun_eq_intro
        (take y : Mem Y,
          obtain (x : Mem X) (Hx : f x = y), from Hs y,
          have f (g y) = f (g' y), from calc
            f (g y) = f (g (f x)) : {Hx⁻¹}
            ... = f x : {fun_eq_elim HL x}
            ... = f (g' (f x)) : fun_eq_elim HR (f x)
            ... = f (g' y) : {Hx},
          show g y = g' y, from Hi this)

    proposition bijective_iff_invertible : bijective f ↔ invertible f :=
      iff.intro
        (assume Hf : bijective f,
          by_cases
            (suppose X = ∅,
              empty_invertible this (and.right Hf))
            (suppose X ≠ ∅,
              obtain (g : Y => X) (HL : left_inverse f g), from
                left_of_nonempty_of_injective this (and.left Hf),
              obtain (g' : Y => X) (HR : left_inverse g' f), from
                right_of_surjective (and.right Hf),
              have g = g', from left_eq_right Hf HL HR,
              have left_inverse g f, from this⁻¹ ▸ HR,
              have f ~~ g, from iff.mpr inverse_iff_both (and.intro HL this),
              show invertible f, from exists.intro g this))
        (suppose invertible f,
          obtain (g : Y => X) (H : f ~~ g), from this,
          have left_inverse f g ∧ left_inverse g f, from
            iff.mp inverse_iff_both H,
          have HL : ∃ g : Y => X, left_inverse f g, from
            exists.intro g (and.left this),
          have HR : ∃ g : Y => X, left_inverse g f, from
            exists.intro g (and.right this),
          have Hi : injective f, from injective_of_left HL,
          have Hs : surjective f, from surjective_of_right HR,
          show bijective f, from and.intro Hi Hs)
  end more_inverse_properties

  -- Exercise 3.3.1
  section equivalence
    variables {X Y : Set} {f g h : X => Y}

    -- Reflexive
    example : f = f :=
      fun_eq_intro (take x : Mem X, rfl)

    -- Symmetric
    example (H : f = g) : g = f :=
      fun_eq_intro
        (take x : Mem X,
          have f x = g x, from fun_eq_elim H x,
          show g x = f x, from this⁻¹)

    -- Transitive
    example (H₁ : f = g) (H₂ : g = h) : f = h :=
      fun_eq_intro
        (take x : Mem X,
          have H₁' : f x = g x, from fun_eq_elim H₁ x,
          have H₂' : g x = h x, from fun_eq_elim H₂ x,
          show f x = h x, from H₂' ▸ H₁')
  end equivalence

  -- Exercise 3.3.2
  section
    variables {X Y Z : Set} {f : X => Y} {g : Y => Z}

    example (H₁ : injective f) (H₂ : injective g) : injective (g ∘ f) :=
      take x x' : Mem X,
      suppose (g ∘ f) x = (g ∘ f) x',
      have g (f x) = g (f x'), from this,
      have f x = f x', from H₂ this,
      show x = x', from H₁ this

    example (H₁ : surjective f) (H₂ : surjective g) : surjective (g ∘ f) :=
      take z : Mem Z,
      obtain (y : Mem Y) (Hy : g y = z), from H₂ z,
      obtain (x : Mem X) (Hx : f x = y), from H₁ y,
      have (g ∘ f) x = z, from calc
        (g ∘ f) x = g (f x) : rfl
        ... = g y : {Hx}
        ... = z : Hy,
      show ∃ x : Mem X, (g ∘ f) x = z, from exists.intro x this
  end

  -- Exercise 3.3.3
  section empty_function
    parameters {X : Set}

    definition empty_fun : ∅ => X :=
      λ e : Mem ∅, absurd e.2 not_in_empty

    proposition empty_fun_inj : injective empty_fun :=
      take e e' : Mem ∅,
      show empty_fun e = empty_fun e' → e = e', from absurd e.2 not_in_empty

    proposition empty_fun_surj : surjective empty_fun ↔ X = ∅ :=
      iff.intro
        (assume H : surjective empty_fun,
          show X = ∅, from by_contradiction
            (suppose X ≠ ∅,
              have x : Mem X, from single_choice_mem this,
              obtain (e : Mem ∅) He, from H x,
              absurd e.2 not_in_empty))
        (suppose X = ∅,
          take x : Mem X,
          have x.1 ∈ ∅, from this ▸ x.2,
          show ∃ e : Mem ∅, empty_fun e = x, from absurd this not_in_empty)

    proposition empty_fun_bij : bijective empty_fun ↔ X = ∅ :=
      iff.intro
        (suppose bijective empty_fun,
          have surjective empty_fun, from and.right this,
          show X = ∅, from iff.mp empty_fun_surj this)
        (suppose X = ∅,
          have surjective empty_fun, from iff.mpr empty_fun_surj this,
          show bijective empty_fun, from and.intro empty_fun_inj this)
  end empty_function

  -- Exercise 3.3.4
  section cancel
    variables {X Y Z : Set} {f f' : X => Y} {g g' : Y => Z}

    example (H₁ : g ∘ f = g ∘ f') (H₂ : injective g) : f = f' :=
      fun_eq_intro
        (take x : Mem X,
          have g (f x) = g (f' x), from fun_eq_elim H₁ x,
          show f x = f' x, from H₂ this)

    example (H₁ : g ∘ f = g' ∘ f) (H₂ : surjective f) : g = g' :=
      fun_eq_intro
        (take y : Mem Y,
          obtain (x : Mem X) (Hx : f x = y), from H₂ y,
          have g (f x) = g' (f x), from fun_eq_elim H₁ x,
          show g y = g' y, from Hx ▸ this)
  end cancel

  -- Exercise 3.3.5
  section
    variables {X Y Z : Set} {f : X => Y} {g : Y => Z}

    example (H : injective (g ∘ f)) : injective f :=
      take x x' : Mem X,
      suppose f x = f x',
      have g (f x) = g (f x'), from this ▸ rfl,
      show x = x', from H this

    example (H : surjective (g ∘ f)) : surjective g :=
      take z : Mem Z,
      obtain (x : Mem X) (Hx : g (f x) = z), from H z,
      show ∃ y : Mem Y, g y = z, from exists.intro (f x) Hx
  end
end set
