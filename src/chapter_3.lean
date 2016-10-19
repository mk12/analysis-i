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
  local abbreviation Set := set Object

  -- Axiom 3.1: Sets are objects
  axiom A1 : ∀ (A : Set) (B : set Set), has_type Prop (A ∈ B)

  -- Definition 3.1.4: Equality of sets
  axiom set_eq {A B : Set} : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B

  -- Convenient way of demonstrating equality
  proposition set_eq_intro {A B : Set}
      (H1 : ∀ x, x ∈ A → x ∈ B) (H2 : ∀ x, x ∈ B → x ∈ A) : A = B :=
    have ∀ x, x ∈ A ↔ x ∈ B, from
      take x,
      iff.intro (H1 x) (H2 x),
    show A = B, from iff.mpr set_eq this

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
        have H1 : ∀ x, x ∉ A, from dm_forall_not this,
        have A = ∅, from no_elements H1,
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

    proposition subset_antisymm (H1 : A ⊆ B) (H2 : B ⊆ A) : A = B :=
      set_eq_intro H1 H2

    proposition subset_trans (H1 : A ⊆ B) (H2 : B ⊆ C) : A ⊆ C :=
      take a,
      suppose a ∈ A,
      have a ∈ B, from H1 this,
      show a ∈ C, from H2 this

    proposition psubset_trans (H1 : A ⊂ B) (H2 : B ⊂ C) : A ⊂ C :=
      have H1' : A ⊆ B, from and.left H1,
      have H2' : B ⊆ C, from and.left H2,
      have A ⊆ C, from subset_trans H1' H2',
      have A ≠ C, from
        suppose A = C,
        have H3 : C ⊆ A, from subset_of_eq this⁻¹,
        have A = B, from set_eq_intro
          (take x, suppose x ∈ A, H1' this)
          (take x, suppose x ∈ B, H3 (H2' this)),
        absurd this (and.right H1),
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
              have H1 : x ∈ (A ∪ B), from or.inr (and.left this),
              have H2 : x ∈ (A ∪ C), from or.inr (and.right this),
              show x ∈ (A ∪ B) ∩ (A ∪ C), from and.intro H1 H2))
        (take x,
          suppose x ∈ (A ∪ B) ∩ (A ∪ C),
          have H1 : x ∈ A ∪ B, from and.left this,
          have H2 : x ∈ A ∪ C, from and.right this,
          show x ∈ A ∪ (B ∩ C), from by_cases
            (suppose x ∈ A, or.inl this)
            (suppose x ∉ A,
              have x ∈ B, from or.resolve_left H1 `x ∉ A`,
              have x ∈ C, from or.resolve_left H2 `x ∉ A`,
              have x ∈ B ∩ C, from and.intro `x ∈ B` `x ∈ C`,
              show x ∈ A ∪ (B ∩ C), from or.inr this))

    proposition inter_distrib : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
      set_eq_intro
        (take x,
          suppose x ∈ A ∩ (B ∪ C),
          have H1 : x ∈ A, from and.left this,
          have H2 : x ∈ B ∪ C, from and.right this,
          show x ∈ (A ∩ B) ∪ (A ∩ C), from or.elim H2
            (suppose x ∈ B, or.inl (and.intro H1 this))
            (suppose x ∈ C, or.inr (and.intro H1 this)))
        (take x,
          suppose x ∈ (A ∩ B) ∪ (A ∩ C),
          show x ∈ A ∩ (B ∪ C), from or.elim this
            (suppose x ∈ A ∩ B,
              have H1 : x ∈ A, from and.left this,
              have H2 : x ∈ B, from and.right this,
              show x ∈ A ∩ (B ∪ C), from and.intro H1 (or.inl H2))
            (suppose x ∈ A ∩ C,
              have H1 : x ∈ A, from and.left this,
              have H2 : x ∈ C, from and.right this,
              show x ∈ A ∩ (B ∪ C), from and.intro H1 (or.inr H2)))

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
          have H1 : x ∈ X, from and.left this,
          have x ∉ A ∪ B, from and.right this,
          have H2 : x ∉ A ∧ x ∉ B, from dm_not_and_not this,
          have H3 : x ∈ X \ A, from and.intro H1 (and.left H2),
          have H4 : x ∈ X \ B, from and.intro H1 (and.right H2),
          show x ∈ (X \ A) ∩ (X \ B), from and.intro H3 H4)
        (take x,
          suppose x ∈ (X \ A) ∩ (X \ B),
          have H1 : x ∈ X, from and.left (and.left this),
          have H2 : x ∉ A, from and.right (and.left this),
          have H3 : x ∉ B, from and.right (and.right this),
          have x ∉ A ∪ B, from dm_not_or (and.intro H2 H3),
          show x ∈ X \ (A ∪ B), from and.intro H1 this)

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
              have H1 : x ∈ X, from and.left this,
              have x ∉ A, from and.right this,
              have x ∉ A ∨ x ∉ B, from or.inl this,
              have H2 : x ∉ A ∩ B, from dm_not_and this,
              show x ∈ X \ (A ∩ B), from and.intro H1 H2)
            (suppose x ∈ X \ B,
              have H1 : x ∈ X, from and.left this,
              have x ∉ B, from and.right this,
              have x ∉ A ∨ x ∉ B, from or.inr this,
              have H2 : x ∉ A ∩ B, from dm_not_and this,
              show x ∈ X \ (A ∩ B), from and.intro H1 H2))
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
        have x ∈ A ↔ x ∈ B, from iff.mp set_eq H x,
        show x ∈ B ↔ x ∈ A, from iff.symm this,
      show B = A, from iff.mpr set_eq this

    -- Transitive
    example (H1 : A = B) (H2 : B = C) : A = C :=
      have H1' : ∀ {x}, x ∈ A ↔ x ∈ B, from iff.mp set_eq H1,
      have H2' : ∀ {x}, x ∈ B ↔ x ∈ C, from iff.mp set_eq H2,
      show A = C, from set_eq_intro
        (take x, suppose x ∈ A, iff.mp H2' (iff.mp H1' this))
        (take x, suppose x ∈ C, iff.mpr H1' (iff.mpr H2' this))
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
          have H1 : C ⊆ A, from and.left this,
          have H2 : C ⊆ B, from and.right this,
          show C ⊆ A ∩ B, from
            take x,
            suppose x ∈ C,
            show x ∈ A ∧ x ∈ B, from and.intro (H1 this) (H2 this))
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
    premises (H1 : A ∪ B = X) (H2 : A ∩ B = ∅)

    private proposition inverse_one : A = X \ B :=
      set_eq_intro
        (take x,
          suppose x ∈ A,
          have x ∈ X, from H1 ▸ or.inl this,
          have x ∉ B, from
            suppose x ∈ B,
            have x ∈ A ∩ B, from and.intro `x ∈ A` `x ∈ B`,
            have x ∈ ∅, from H2 ▸ this,
            absurd this not_in_empty,
          show x ∈ X \ B, from and.intro `x ∈ X` `x ∉ B`)
        (take x,
          suppose x ∈ X \ B,
          have H3 : x ∈ A ∪ B, from H1⁻¹ ▸ and.left this,
          have H4 : x ∉ B, from and.right this,
          show x ∈ A, from by_contradiction
            (suppose x ∉ A,
              have x ∉ A ∧ x ∉ B, from and.intro this H4,
              have x ∉ A ∪ B, from dm_not_or this,
              absurd H3 this))

    private proposition inverse_two : B = X \ A :=
      inverse_one (union_comm ▸ H1) (inter_comm ▸ H2)
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

  -- Definition 3.3.1: Functions
  definition Fun (X Y : Set) : Type := Mem X → Mem Y
  infixr ` => `:25 := Fun

  -- Definition 3.3.7: Equality of functions
  axiom fun_eq {X Y : Set} {f g : X => Y} : f = g ↔ ∀ x : Mem X, f x = g x

  -- Convenient way of demonstrating equality
  proposition fun_eq_intro {X Y : Set} {f g : X => Y}
      (H : ∀ x : Mem X, f x = g x) : f = g :=
    iff.mpr fun_eq H

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
  definition bijective {X Y : Set} (f : X => Y) :=
    injective f ∧ surjective f

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
          have f x = g x, from iff.mp fun_eq H x,
          show g x = f x, from this⁻¹)

    -- Transitive
    example (H1 : f = g) (H2 : g = h) : f = h :=
      fun_eq_intro
        (take x : Mem X,
          have H1' : f x = g x, from iff.mp fun_eq H1 x,
          have H2' : g x = h x, from iff.mp fun_eq H2 x,
          show f x = h x, from H2' ▸ H1')
  end equivalence

  -- Exercise 3.3.2
  section
    variables {X Y Z : Set} {f : X => Y} {g : Y => Z}

    example (H1 : injective f) (H2 : injective g) : injective (g ∘ f) :=
      take x x' : Mem X,
      suppose (g ∘ f) x = (g ∘ f) x',
      have g (f x) = g (f x'), from this,
      have f x = f x', from H2 this,
      show x = x', from H1 this

    example (H1 : surjective f) (H2 : surjective g) : surjective (g ∘ f) :=
      take z : Mem Z,
      obtain (y : Mem Y) (Hy : g y = z), from H2 z,
      obtain (x : Mem X) (Hx : f x = y), from H1 y,
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
              obtain a (Ha : a ∈ X), from single_choice this,
              have x : Mem X, from dpair a Ha,
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
end set
