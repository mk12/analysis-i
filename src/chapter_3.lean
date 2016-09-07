-- Copyright 2016 Mitchell Kember. Subject to the MIT License.
-- Formalization of Analysis I: Chapter 3

import .common .chapter_2

open classical eq.ops

-- A set is defined as a membership predicate
definition set (X : Type) := X → Prop

namespace set
  -- Basic definitions
  section basic
    variable {X : Type}

    definition mem (x : X) (A : set X) : Prop := A x
    definition empty : set X := λ x, false

    infix `∈` := mem
    notation a `∉` s := ¬ mem a s
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
  infix `∪` := union

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
  definition subset (A B : Set) := ∀ {{x}}, x ∈ A → x ∈ B
  infix `⊆` := subset
  definition proper_subset (A B : Set) := A ⊆ B ∧ A ≠ B
  infix `⊂`:50 := proper_subset

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
  infix `∩` := inter

  -- Definition 3.1.26: Difference sets
  definition diff (A B : Set) : Set := λ x, x ∈ A ∧ x ∉ B
  infix `\`:70 := diff

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

  -- Exercise 3.1.5
  section equivalence
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
  end equivalence
end set
