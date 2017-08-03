-- Copyright 2016 Mitchell Kember. Subject to the MIT ficense.
-- Formalization of Analysis I: Chapter 3

import .common .chapter_2

open classical (by_cases by_contradiction)

namespace chapter_3

-- Definition 3.1.1: A set is an unordered collection of objects
def set (α : Type) : Type := α → Prop

namespace set
section object
  parameter Object : Type

  @[reducible]
  def Set := set Object

  -- Set membership
  def mem (x : Object) (A : Set) : Prop := A x
  instance : has_mem Object Set := ⟨mem⟩

  -- Axiom 3.1: Sets are objects
  example (A : Set) (B : set Set) : Prop := A ∈ B

  -- Definition 3.1.4: Equality of sets
  theorem set_eq {A B : Set} : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B :=
    iff.intro
      (assume (H : A = B) x,
        show x ∈ A ↔ x ∈ B, from iff.intro
          (suppose x ∈ A, H ▸ this)
          (suppose x ∈ B, H.symm ▸ this))
      (suppose ∀ x, x ∈ A ↔ x ∈ B,
        have ∀ x, (x ∈ A) = (x ∈ B), from
          assume x, (this x).to_eq,
        show A = B, from funext this)

  -- Introduction and elimination rules
  section intro_elim
    variables {A B : Set}

    theorem set_eq_intro
        (H₁ : ∀ x, x ∈ A → x ∈ B) (H₂ : ∀ x, x ∈ B → x ∈ A) : A = B :=
      have ∀ x, x ∈ A ↔ x ∈ B, from
        assume x, ⟨H₁ x, H₂ x⟩,
      show A = B, from set_eq.mpr this

    theorem set_eq_elim : A = B → ∀ x, x ∈ A ↔ x ∈ B :=
      set_eq.mp
  end intro_elim

  -- Axiom 3.2: Empty set
  def empty : Set := λ _, false
  instance : has_emptyc Set := ⟨empty⟩
  theorem not_in_empty {x : Object} : x ∉ (∅ : Set) := id

  -- Convenient way of demonstrating emptiness
  theorem no_elements {A : Set} (H : ∀ x, x ∉ A) : A = ∅ :=
    set_eq_intro
      (assume x (Hx : x ∈ A), absurd Hx (H x))
      (assume x (Hx : x ∈ ∅), absurd Hx not_in_empty)

  -- Lemma 3.1.6: Single choice
  lemma single_choice {A : Set} (H : A ≠ ∅) : ∃ x, x ∈ A :=
    by_contradiction
      (suppose ¬ ∃ x, x ∈ A,
        have ∀ x, x ∉ A, from dm_forall_not this,
        have A = ∅, from no_elements this,
        absurd this H)

  -- Axiom 3.3: Singleton sets
  def singleton (x : Object) : Set := λ y, x = y

  -- Axiom 3.4: Pairwise union
  def union (A B : Set) : Set := λ x, x ∈ A ∨ x ∈ B
  instance : has_union Set := ⟨union⟩

  -- Lemma 3.1.12
  section union_properties
    variables {A B C : Set}

    lemma union_comm : A ∪ B = B ∪ A :=
      set_eq_intro
        (assume x (H : x ∈ A ∪ B), H.swap)
        (assume x (H : x ∈ B ∪ A), H.swap)

    lemma union_assoc : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
      set_eq_intro
        (assume x (H : x ∈ (A ∪ B) ∪ C), or.assoc.mp H)
        (assume x (H : x ∈ A ∪ (B ∪ C)), or.assoc.mpr H)

    lemma union_idemp : A ∪ A = A :=
      set_eq_intro
        (assume x (H : x ∈ A ∪ A), H.elim id id)
        (assume x (H : x ∈ A), or.inl H)

    lemma union_empty : A ∪ ∅ = A :=
      set_eq_intro
        (assume x (H : x ∈ A ∪ ∅), H.elim id false.elim)
        (assume x (H : x ∈ A), or.inl H)
  end union_properties

  -- Definition 3.1.14: Subsets
  definition subset (A B : Set) : Prop := ∀ {{x}}, x ∈ A → x ∈ B
  instance : has_subset Set := ⟨subset⟩
  definition proper_subset (A B : Set) : Prop := A ⊆ B ∧ A ≠ B
  instance : has_ssubset Set := ⟨proper_subset⟩

  -- Proposition 3.1.17: Sets are partially ordered by set inclusion
  section subset_properties
    variables {A B C : Set}

    theorem subset_of_eq (H : A = B) : A ⊆ B :=
      assume a (Ha : a ∈ A),
      show a ∈ B, from H ▸ Ha

    theorem subset_rfl : A ⊆ A := subset_of_eq rfl

    theorem subset_antisymm (H₁ : A ⊆ B) (H₂ : B ⊆ A) : A = B :=
      set_eq_intro H₁ H₂

    theorem subset_trans (H₁ : A ⊆ B) (H₂ : B ⊆ C) : A ⊆ C :=
      assume a (Ha : a ∈ A),
      have a ∈ B, from H₁ Ha,
      show a ∈ C, from H₂ this

    theorem proper_subset_trans (H₁ : A ⊂ B) (H₂ : B ⊂ C) : A ⊂ C :=
      have H₁' : A ⊆ B, from H₁.left,
      have H₂' : B ⊆ C, from H₂.left,
      have A ≠ C, from
        suppose A = C,
        have H₃ : C ⊆ A, from subset_of_eq this.symm,
        have A = B, from set_eq_intro
          (assume x (Hx : x ∈ A), H₁' Hx)
          (assume x (Hx : x ∈ B), H₃ (H₂' Hx)),
        absurd this H₁.right,
      show A ⊂ C, from ⟨subset_trans H₁' H₂', this⟩
  end subset_properties

  -- Axiom 3.5: Axiom of specification
  def specify (A : Set) (p : Object → Prop) : Set := λ x, x ∈ A ∧ p x

  -- Definition 3.1.22: Intersections
  def inter (A B : Set) : Set := λ x, x ∈ A ∧ x ∈ B
  instance : has_inter Set := ⟨inter⟩

  -- Definition 3.1.26: Difference sets
  def diff (A B : Set) : Set := λ x, x ∈ A ∧ x ∉ B
  instance : has_sdiff Set := ⟨diff⟩

  -- Proposition 3.1.27: Sets form a boolean algebra
  section boolean_algebra
    variables {A B C X : Set}
    variables (HA : A ⊆ X) (HB : B ⊆ X) (HC : C ⊆ X)

    -- Minimal element

    example : A ∪ ∅ = A := union_empty

    theorem inter_empty : A ∩ ∅ = ∅ :=
      no_elements
        (assume x (Hx : x ∈ A ∩ ∅), absurd Hx.right not_in_empty)

    -- Maximal element

    theorem union_super : A ∪ X = X :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∪ X), Hx.elim (@HA x) id)
        (assume x (Hx : x ∈ X), or.inr Hx)

    theorem inter_super : A ∩ X = A :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∩ X), Hx.left)
        (assume x (Hx : x ∈ A), ⟨Hx, HA Hx⟩)

    -- Identity

    example : A ∪ A = A := union_idemp

    theorem inter_idemp : A ∩ A = A :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∩ A), Hx.left)
        (assume x (Hx : x ∈ A), ⟨Hx, Hx⟩)

    -- Commutativity

    example : A ∪ B = B ∪ A := union_comm

    theorem inter_comm : A ∩ B = B ∩ A :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∩ B), Hx.swap)
        (assume x (Hx : x ∈ B ∩ A), Hx.swap)

    -- Associativity

    example : (A ∪ B) ∪ C = A ∪ (B ∪ C) := union_assoc

    theorem inter_assoc : (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
      set_eq_intro
        (assume x (Hx : x ∈ (A ∩ B) ∩ C), and.assoc.mp Hx)
        (assume x (Hx : x ∈ A ∩ (B ∩ C)), and.assoc.mpr Hx)

    -- Distributivity

    theorem union_distrib : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∪ (B ∩ C)),
          show x ∈ (A ∪ B) ∩ (A ∪ C), from Hx.elim
            (suppose x ∈ A, ⟨or.inl this, or.inl this⟩)
            (suppose x ∈ B ∩ C, ⟨or.inr this.left, or.inr this.right⟩))
        (assume x (Hx : x ∈ (A ∪ B) ∩ (A ∪ C)),
          show x ∈ A ∪ (B ∩ C), from by_cases
            (suppose x ∈ A, or.inl this)
            (suppose x ∉ A,
              have H₁ : x ∈ B, from Hx.left.resolve_left this,
              have H₂ : x ∈ C, from Hx.right.resolve_left this,
              show x ∈ A ∪ (B ∩ C), from or.inr ⟨H₁, H₂⟩))

    theorem inter_distrib : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∩ (B ∪ C)),
          show x ∈ (A ∩ B) ∪ (A ∩ C), from Hx.right.elim
            (suppose x ∈ B, or.inl ⟨Hx.left, this⟩)
            (suppose x ∈ C, or.inr ⟨Hx.left, this⟩))
        (assume x (Hx : x ∈ (A ∩ B) ∪ (A ∩ C)),
          show x ∈ A ∩ (B ∪ C), from Hx.elim
            (suppose x ∈ A ∩ B, ⟨this.left, or.inl this.right⟩)
            (suppose x ∈ A ∩ C, ⟨this.left, or.inr this.right⟩))

    -- Partition

    theorem union_partition : A ∪ (X \ A) = X :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∪ (X \ A)),
          show x ∈ X, from or.elim Hx (@HA x) and.left)
        (assume x (Hx : x ∈ X),
          show x ∈ A ∪ (X \ A), from by_cases
            (suppose x ∈ A, or.inl this)
            (suppose x ∉ A, or.inr ⟨Hx, this⟩))

    theorem inter_partition : A ∩ (X \ A) = ∅ :=
      no_elements
        (assume x (Hx : x ∈ A ∩ (X \ A)),
          absurd Hx.left Hx.right.right)

    -- De Morgan laws

    theorem union_dm : X \ (A ∪ B) = (X \ A) ∩ (X \ B) :=
      set_eq_intro
        (assume x (Hx : x ∈ X \ (A ∪ B)),
          have x ∉ A ∧ x ∉ B, from dm_not_and_not Hx.right,
          have H₁ : x ∈ X \ A, from ⟨Hx.left, this.left⟩,
          have H₂ : x ∈ X \ B, from ⟨Hx.left, this.right⟩,
          show x ∈ (X \ A) ∩ (X \ B), from ⟨H₁, H₂⟩)
        (assume x (Hx : x ∈ (X \ A) ∩ (X \ B)),
          have x ∉ A ∧ x ∉ B, from ⟨Hx.left.right, Hx.right.right⟩,
          have x ∉ A ∪ B, from dm_not_or this,
          show x ∈ X \ (A ∪ B), from ⟨Hx.left.left, this⟩)

    theorem inter_dm : X \ (A ∩ B) = (X \ A) ∪ (X \ B) :=
      set_eq_intro
        (assume x (Hx : x ∈ X \ (A ∩ B)),
          have x ∉ A ∨ x ∉ B, from dm_not_or_not Hx.right,
          show x ∈ (X \ A) ∪ (X \ B), from this.elim
            (suppose x ∉ A, or.inl ⟨Hx.left, this⟩)
            (suppose x ∉ B, or.inr ⟨Hx.left, this⟩))
        (assume x (Hx : x ∈ (X \ A) ∪ (X \ B)),
          show x ∈ X \ (A ∩ B), from Hx.elim
            (suppose x ∈ X \ A,
              have H₁ : x ∈ X, from this.left,
              have x ∉ A ∨ x ∉ B, from or.inl this.right,
              have x ∉ A ∩ B, from dm_not_and this,
              show x ∈ X \ (A ∩ B), from ⟨H₁, this⟩)
            (suppose x ∈ X \ B,
              have H₁ : x ∈ X, from this.left,
              have x ∉ A ∨ x ∉ B, from or.inr this.right,
              have x ∉ A ∩ B, from dm_not_and this,
              show x ∈ X \ (A ∩ B), from ⟨H₁, this⟩))
  end boolean_algebra

  -- Axiom 3.6: Replacement
  def replace (A : Set) (p : Object → Object → Prop) : Set :=
    λ y, ∃ x, x ∈ A ∧ p x y

  -- More convenient form of Axiom 3.6
  def map (A : Set) (f : Object → Object) : Set :=
    replace A (λ x y, y = f x)

  -- Axiom 3.7: Infinity
  def infinity : set chapter_2.N := λ x, true

  -- Exercise 3.1.1
  section equivalence
    variables {A B C : Set}

    -- Reflexive
    example : A = A :=
      set_eq_intro
        (assume x (Hx : x ∈ A), Hx)
        (assume x (Hx : x ∈ A), Hx)

    -- Symmetric
    example (H : A = B) : B = A :=
      have ∀ x, x ∈ B ↔ x ∈ A, from
        assume x, (set_eq_elim H x).symm,
      show B = A, from set_eq.mpr this

    -- Transitive
    example (H₁ : A = B) (H₂ : B = C) : A = C :=
      have H₁' : ∀ {x}, x ∈ A ↔ x ∈ B, from set_eq_elim H₁,
      have H₂' : ∀ {x}, x ∈ B ↔ x ∈ C, from set_eq_elim H₂,
      show A = C, from set_eq_intro
        (assume x (Hx : x ∈ A), H₂'.mp (H₁'.mp Hx))
        (assume x (Hx : x ∈ C), H₁'.mpr (H₂'.mpr Hx))
  end equivalence

  -- Exercise 3.1.5
  section
    variables {A B : Set}

    -- (1) → (2)
    example (H : A ⊆ B) : A ∪ B = B :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∪ B), or.elim Hx (@H x) id)
        (assume x (Hx : x ∈ B), or.inr Hx)

    -- (2) → (3)
    example (H : A ∪ B = B) : A ∩ B = A :=
      have H' : A ∪ B ⊆ B, from subset_of_eq H,
      set_eq_intro
        (assume x (Hx : x ∈ A ∩ B), Hx.left)
        (assume x (Hx : x ∈ A), ⟨Hx, H' (or.inl Hx)⟩)

    -- (3) → (1)
    example (H : A ∩ B = A) : A ⊆ B :=
      have H' : A ⊆ A ∩ B, from subset_of_eq H.symm,
      assume x (Hx : x ∈ A),
      have x ∈ A ∩ B, from H' Hx,
      show x ∈ B, from this.right
  end

  -- Exercise 3.1.7
  section
    variables {A B C : Set}

    theorem inter_subset_left : A ∩ B ⊆ A :=
      assume x (Hx : x ∈ A ∩ B),
      show x ∈ A, from Hx.left

    theorem inter_subset_right : A ∩ B ⊆ B :=
      assume x (Hx : x ∈ A ∩ B),
      show x ∈ B, from Hx.right

    example : C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B :=
      iff.intro
        (assume H : C ⊆ A ∧ C ⊆ B,
          show C ⊆ A ∩ B, from
            assume x (Hx : x ∈ C),
            show x ∈ A ∧ x ∈ B, from ⟨H.left Hx, H.right Hx⟩)
        (assume H : C ⊆ A ∩ B,
          have H₁ : C ⊆ A, from
            assume x (Hx : x ∈ C),
            show x ∈ A, from (H Hx).left,
          have H₂ : C ⊆ B, from
            assume x (Hx : x ∈ C),
            show x ∈ B, from (H Hx).right,
          show C ⊆ A ∧ C ⊆ B, from ⟨H₁, H₂⟩)

    theorem subset_union_left : A ⊆ A ∪ B :=
      assume x (Hx : x ∈ A),
      show x ∈ A ∪ B, from or.inl Hx

    theorem subset_union_right : B ⊆ A ∪ B :=
      assume x (Hx : x ∈ B),
      show x ∈ A ∪ B, from or.inr Hx

    example : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C :=
      iff.intro
        (assume H : A ⊆ C ∧ B ⊆ C,
          show A ∪ B ⊆ C, from
            assume x (Hx : x ∈ A ∪ B),
            show x ∈ C, from or.elim Hx
              (suppose x ∈ A, H.left this)
              (suppose x ∈ B, H.right this))
        (assume H : A ∪ B ⊆ C,
          have H₁ : A ⊆ C, from
            assume x (Hx : x ∈ A),
            show x ∈ C, from H (or.inl Hx),
          have H₂ : B ⊆ C, from
            assume x (Hx : x ∈ B),
            show x ∈ C, from H (or.inr Hx),
          show A ⊆ C ∧ B ⊆ C, from ⟨H₁, H₂⟩)
  end

  -- Exercise 3.1.8
  section absorption
    variables {A B : Set}

    example : A ∩ (A ∪ B) = A :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∩ (A ∪ B)), and.left Hx)
        (assume x (Hx : x ∈ A), ⟨Hx, or.inl Hx⟩)

    example : A ∪ (A ∩ B) = A :=
      set_eq_intro
        (assume x (Hx : x ∈ A ∪ (A ∩ B)), or.elim Hx id and.left)
        (assume x (Hx : x ∈ A), or.inl Hx)
  end absorption

  -- Exercise 3.1.9
  section
    variables {A B X : Set}
    variables (Hu : A ∪ B = X) (Hi : A ∩ B = ∅)

    theorem set_complement_left : A = X \ B :=
      set_eq_intro
        (assume x (Hx : x ∈ A),
          have x ∈ A ∪ B, from or.inl Hx,
          have H₁ : x ∈ X, from subset_of_eq Hu this,
          have H₂ : x ∉ B, from
            suppose x ∈ B,
            have x ∈ A ∩ B, from ⟨Hx, this⟩,
            have x ∈ ∅, from subset_of_eq Hi this,
            absurd this not_in_empty,
          show x ∈ X \ B, from ⟨H₁, H₂⟩)
        (take x,
          suppose x ∈ X \ B,
          have H₁ : x ∈ A ∪ B, from subset_of_eq Hu.symm this.left,
          have H₂ : x ∉ B, from this.right,
          show x ∈ A, from by_contradiction
            (suppose x ∉ A,
              have x ∉ A ∧ x ∉ B, from ⟨this, H₂⟩,
              have x ∉ A ∪ B, from dm_not_or this,
              absurd H₁ this))

    theorem set_complement_right : B = X \ A :=
      have Hu' : B ∪ A = X, from (@union_comm A B) ▸ Hu,
      have Hi' : B ∩ A = ∅, from (@inter_comm A B) ▸ Hi,
      set_complement_left Hu' Hi'
  end

  -- Exercise 3.1.10
  section
    variables {A B : Set}

    example : (A \ B) ∩ (B \ A) = ∅ :=
      no_elements
        (assume x (Hx : x ∈ (A \ B) ∩ (B \ A)),
          have H₁ : x ∈ A, from and.left (and.left Hx),
          have H₂ : x ∉ A, from and.right (and.right Hx),
          absurd H₁ H₂)

    example : (A \ B) ∩ (A ∩ B) = ∅ :=
      no_elements
        (assume x (Hx : x ∈ (A \ B) ∩ (A ∩ B)),
          have H₁ : x ∈ B, from and.right (and.right Hx),
          have H₂ : x ∉ B, from and.right (and.left Hx),
          absurd H₁ H₂)

    example : (B \ A) ∩ (A ∩ B) = ∅ :=
      no_elements
        (assume x (Hx : x ∈ (B \ A) ∩ (A ∩ B)),
          have H₁ : x ∈ A, from and.left (and.right Hx),
          have H₂ : x ∉ A, from and.right (and.left Hx),
          absurd H₁ H₂)

    example : (A \ B) ∪ (A ∩ B) ∪ (B \ A) = A ∪ B :=
      set_eq_intro
        (assume x (H : x ∈ (A \ B) ∪ (A ∩ B) ∪ (B \ A)),
          show x ∈ A ∪ B, from or.elim H
            (suppose x ∈ (A \ B) ∪ (A ∩ B), or.elim this
              (suppose x ∈ A \ B, or.inl (and.left this))
              (suppose x ∈ A ∩ B, or.inl (and.left this)))
            (suppose x ∈ B \ A, or.inr (and.left this)))
        (assume x (H : x ∈ A ∪ B),
          show x ∈ (A \ B) ∪ (A ∩ B) ∪ (B \ A), from or.elim H
            (assume H : x ∈ A, by_cases
              (suppose x ∈ B, or.inl (or.inr ⟨H, this⟩))
              (suppose x ∉ B, or.inl (or.inl ⟨H, this⟩)))
            (assume H : x ∈ B, by_cases
              (suppose x ∈ A, or.inl (or.inr ⟨this, H⟩))
              (suppose x ∉ A, or.inr ⟨H, this⟩)))
  end

  -- Some miscellaneous set properties
  section misc
    variables {x : Object} {A B : Set}

    theorem in_union_left (H₁ : x ∈ A ∪ B) (H₂ : x ∉ B) : x ∈ A :=
      or.elim H₁ id (suppose x ∈ B, absurd this H₂)

    theorem in_union_right (H₁ : x ∈ A ∪ B) (H₂ : x ∉ A) : x ∈ B :=
      have x ∈ B ∪ A, from (@union_comm A B) ▸ H₁,
      show x ∈ B, from in_union_left this H₂

    theorem not_in_disjoint_left (H₁ : A ∩ B = ∅) (H₂ : x ∈ B) : x ∉ A :=
      suppose x ∈ A,
      have x ∈ A ∩ B, from ⟨this, H₂⟩,
      have x ∈ ∅, from subset_of_eq H₁ this,
      absurd this not_in_empty

    theorem not_in_disjoint_right (H₁ : A ∩ B = ∅) (H₂ : x ∈ A) : x ∉ B :=
      have B ∩ A = ∅, from (@inter_comm A B) ▸ H₁,
      show x ∉ B, from not_in_disjoint_left this H₂
  end misc

/-
  -- Convert Set to Type using dependent pairs
  definition Mem (X : Set) : Type := Σ x, x ∈ X

  -- Constructor for Mem
  definition Mem.mk {X : Set} {x : Object} (H : x ∈ X) : Mem X :=
    sigma.mk x H

  -- Eta expansion and reduction
  definition eta_exp {X : Set} (x : Mem X) : x = Mem.mk x.2 := sigma.eq rfl rfl
  definition eta_red {X : Set} (x : Mem X) : Mem.mk x.2 = x := sigma.eq rfl rfl

  -- Single choice for Mem
  noncomputable definition single_choice_mem {X : Set} (H : X ≠ ∅) : Mem X :=
    have ∃ a, a ∈ X, from single_choice H,
    Mem.mk (some_spec this)

  -- Definition 3.3.1: Functions
  definition Fun (X Y : Set) : Type := Mem X → Mem Y
  infixr ` => `:25 := Fun

  -- Definition 3.3.7: Equality of functions
  proposition fun_eq {X Y : Set} {f g : X => Y} :
      f = g ↔ ∀ x : Mem X, f x = g x :=
    iff.intro
      (suppose f = g,
        take x : Mem X,
        show f x = g x, from this ▸ rfl)
      (suppose ∀ x : Mem X, f x = g x,
        show f = g, from funext this)

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

  -- Convenient way to use injectivity from a bijection
  proposition bleft {X Y : Set} {f : X => Y} (H₁ : bijective f) {x x' : Mem X}
      (H₂ : f x = f x') : x = x' :=
    have injective f, from and.left H₁,
    show x = x', from this H₂

  -- Inverse functions
  section inverse
    variables {X Y : Set}

    definition left_inverse (f : X => Y) (g : Y => X) : Prop := g ∘ f = id
    infix ` <~ `:50 := left_inverse

    definition inverse (f : X => Y) (g : Y => X) : Prop := f <~ g ∧ g <~ f
    infix ` <~> `:50 := inverse

    definition invertible (f : X => Y) : Prop := ∃ g : Y => X, f <~> g
  end inverse

  -- Uniqueness of inverse functions
  section inverse_unique
    parameters {X Y : Set} {f : X => Y}

    proposition inverse_unique (H : invertible f) : ∃! g : Y => X, f <~> g :=
      obtain (g : Y => X) (Hg : f <~> g), from H,
      have ∀ h : Y => X, f <~> h → h = g, from
        take h : Y => X,
        assume Hh : f <~> h,
        show h = g, from fun_eq_intro
          (take y : Mem Y,
            have f (g y) = y, from fun_eq_elim (and.right Hg) y,
            have h (f (g y)) = h y, from this ▸ rfl,
            have g y = h y, from fun_eq_elim (and.left Hh) (g y) ▸ this,
            show h y = g y, from this⁻¹),
      show ∃! g : Y => X, f <~> g, from exists_unique.intro g Hg this

    noncomputable definition the_inverse (H : invertible f) : Y => X :=
      the (inverse_unique H)

    proposition the_inverse_spec (H : invertible f) : f <~> (the_inverse H) :=
      the_spec (inverse_unique H)

    proposition eq_the_inverse {g : Y => X} (H : f <~> g) :
        g = the_inverse (exists.intro g H) :=
      eq_the (inverse_unique (exists.intro g H)) H
  end inverse_unique

  -- Properties of inverse functions
  section inverse_properties
    variables {X Y : Set} {f : X => Y} {g : Y => X}

    -- Symmetry
    proposition inverse_symm (H : f <~> g) : g <~> f :=
      and.swap H

    -- Alternative definition of inverse functions
    proposition inverse_iff_alternative :
        f <~> g ↔ ∀ (x : Mem X) (y : Mem Y), f x = y ↔ g y = x :=
      iff.intro
        (assume H : f <~> g,
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
        (assume H : ∀ (x : Mem X) (y : Mem Y), f x = y ↔ g y = x,
          have HL : f <~ g, from fun_eq_intro
            (take x : Mem X, iff.mp (H x (f x)) rfl),
          have HR : g <~ f, from fun_eq_intro
            (take y : Mem Y, iff.mpr (H (g y) y) rfl),
          show f <~> g, from and.intro HL HR)
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
        ∃ g : Y => X, f <~ g :=
      let g (y : Mem Y) : Mem X :=
        if H : ∃! x : Mem X, f x = y
          then the H
          else single_choice_mem Hn
      in
      have f <~ g, from fun_eq_intro
        (take a : Mem X,
          have ∃ x : Mem X, f x = f a, from exists.intro a rfl,
          have H : ∃! x : Mem X, f x = f a, from unique_of_injective Hi this,
          show g (f a) = a, from calc
            g (f a) = the H : dif_pos H
            ... = a : eq_the H rfl),
      show ∃ g : Y => X, f <~ g, from exists.intro g this

    proposition injective_of_left (H : ∃ g : Y => X, f <~ g) : injective f :=
      obtain (g : Y => X) (HL : f <~ g), from H,
      show injective f, from
        take x x' : Mem X,
        suppose f x = f x',
        show x = x', from calc
          x = g (f x) : fun_eq_elim HL x
          ... = g (f x') : {this}
          ... = x' : fun_eq_elim HL x'

    proposition right_of_surjective (Hs : surjective f) :
        ∃ g : Y => X, g <~ f :=
      let g (y : Mem Y) : Mem X := some (Hs y) in
      have g <~ f, from fun_eq_intro
        (take y : Mem Y,
          show f (g y) = y, from calc
            f (g y) = f (some (Hs y)) : rfl
            ... = y : some_spec (Hs y)),
      show ∃ g : Y => X, g <~ f, from exists.intro g this

    proposition surjective_of_right (H : ∃ g : Y => X, g <~ f) : surjective f :=
      obtain (g : Y => X) (HR : g <~ f), from H,
      show surjective f, from
        take y : Mem Y,
        have f (g y) = y, from fun_eq_elim HR y,
        show ∃ x : Mem X, f x = y, from exists.intro (g y) this

    private lemma empty_invertible (Hn : X = ∅) (Hs : surjective f) :
        invertible f :=
      let g (y : Mem Y) : Mem X := some (Hs y) in
      have HL : f <~ g, from fun_eq_intro
        (take x : Mem X, absurd (Hn ▸ x.2) not_in_empty),
      have HR : g <~ f, from fun_eq_intro
        (take y : Mem Y, absurd (Hn ▸ (g y).2) not_in_empty),
      have f <~> g, from and.intro HL HR,
      show invertible f, from exists.intro g this

    private lemma left_eq_right {g g' : Y => X} (Hf : bijective f) (HL : f <~ g)
        (HR : g' <~ f) : g = g' :=
      fun_eq_intro
        (take y : Mem Y,
          obtain (x : Mem X) (Hx : f x = y), from and.right Hf y,
          have f (g y) = f (g' y), from calc
            f (g y) = f (g (f x)) : {Hx⁻¹}
            ... = f x : {fun_eq_elim HL x}
            ... = f (g' (f x)) : fun_eq_elim HR (f x)
            ... = f (g' y) : {Hx},
          show g y = g' y, from bleft Hf this)

    proposition bijective_iff_invertible : bijective f ↔ invertible f :=
      iff.intro
        (assume Hf : bijective f,
          by_cases
            (suppose X = ∅,
              empty_invertible this (and.right Hf))
            (suppose X ≠ ∅,
              obtain (g : Y => X) (HL : f <~ g), from
                left_of_nonempty_of_injective this (and.left Hf),
              obtain (g' : Y => X) (HR : g' <~ f), from
                right_of_surjective (and.right Hf),
              have g = g', from left_eq_right Hf HL HR,
              have g <~ f, from this⁻¹ ▸ HR,
              have f <~> g, from (and.intro HL this),
              show invertible f, from exists.intro g this))
        (suppose invertible f,
          obtain (g : Y => X) (H : f <~> g), from this,
          have HL : ∃ g : Y => X, f <~ g, from exists.intro g (and.left H),
          have HR : ∃ g : Y => X, g <~ f, from exists.intro g (and.right H),
          have Hi : injective f, from injective_of_left HL,
          have Hs : surjective f, from surjective_of_right HR,
          show bijective f, from and.intro Hi Hs)

    proposition invertible_of_bijective [coercion] (H : bijective f) :
        invertible f :=
      iff.mp bijective_iff_invertible H

    proposition bijective_of_invertible [coercion] (H : invertible f) :
        bijective f :=
      iff.mpr bijective_iff_invertible H
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

    local abbreviation f := @empty_fun

    proposition empty_fun_inj : injective f :=
      take e e' : Mem ∅,
      show f e = f e' → e = e', from absurd e.2 not_in_empty

    proposition empty_fun_surj : surjective f ↔ X = ∅ :=
      iff.intro
        (assume H : surjective f,
          show X = ∅, from by_contradiction
            (suppose X ≠ ∅,
              obtain (e : Mem ∅) He, from H (single_choice_mem this),
              absurd e.2 not_in_empty))
        (suppose X = ∅,
          take x : Mem X,
          show ∃ e : Mem ∅, f e = x, from absurd (this ▸ x.2) not_in_empty)

    proposition empty_fun_bij : bijective f ↔ X = ∅ :=
      iff.intro
        (suppose bijective f,
          have surjective f, from and.right this,
          show X = ∅, from iff.mp empty_fun_surj this)
        (suppose X = ∅,
          have surjective f, from iff.mpr empty_fun_surj this,
          show bijective f, from and.intro empty_fun_inj this)
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

  -- Exercise 3.3.6
  section
    parameters {X Y : Set} {f : X => Y}
    hypothesis Hf : bijective f

    private noncomputable definition fi : Y => X := the_inverse Hf
    private proposition Hfi : f <~> fi := the_inverse_spec Hf

    example (x : Mem X) : fi (f x) = x :=
      have f <~ fi, from and.left Hfi,
      show fi (f x) = x, from fun_eq_elim this x

    example (y : Mem Y) : f (fi y) = y :=
      have fi <~ f, from and.right Hfi,
      show f (fi y) = y, from fun_eq_elim this y

    example : invertible fi :=
      have fi <~> f, from inverse_symm Hfi,
      show invertible fi, from exists.intro f this
  end

  -- Exercise 3.3.7
  section
    parameters {X Y Z : Set} {f : X => Y} {g : Y => Z}
    hypothesis Hf : bijective f
    hypothesis Hg : bijective g

    example : bijective (g ∘ f) :=
      have Hi : injective (g ∘ f), from
        take x x' : Mem X,
        suppose g (f x) = g (f x'),
        have f x = f x', from bleft Hg this,
        show x = x', from bleft Hf this,
      have Hs : surjective (g ∘ f), from
        take z : Mem Z,
        obtain (y : Mem Y) (Hy : g y = z), from and.right Hg z,
        obtain (x : Mem X) (Hx : f x = y), from and.right Hf y,
        show ∃ x : Mem X, g (f x) = z, from exists.intro x (Hx⁻¹ ▸ Hy),
      show bijective (g ∘ f), from and.intro Hi Hs

    private noncomputable definition fi : Y => X := the_inverse Hf
    private noncomputable definition gi : Z => Y := the_inverse Hg
    private proposition Hfi : f <~> fi := the_inverse_spec Hf
    private proposition Hgi : g <~> gi := the_inverse_spec Hg

    example : g ∘ f <~> fi ∘ gi :=
      have HL : g ∘ f <~ fi ∘ gi, from fun_eq_intro
        (take x : Mem X,
          show fi (gi (g (f x))) = x, from calc
            fi (gi (g (f x))) = fi (f x) : {fun_eq_elim (and.left Hgi) (f x)}
            ... = x : fun_eq_elim (and.left Hfi) x),
      have HR : fi ∘ gi <~ g ∘ f, from fun_eq_intro
        (take z : Mem Z,
          show g (f (fi (gi z))) = z, from calc
            g (f (fi (gi z))) = g (gi z) : {fun_eq_elim (and.right Hfi) (gi z)}
            ... = z : fun_eq_elim (and.right Hgi) z),
      show g ∘ f <~> fi ∘ gi, from and.intro HL HR
  end

  -- Exercise 3.3.8
  section inclusion
    definition inclusion_map (X Y : Set) (H : X ⊆ Y) : X => Y :=
      λ x : Mem X, Mem.mk (H x.2)

    local abbreviation ι := @inclusion_map

    section part_1
      parameters {X Y Z : Set}
      hypothesis H₁ : X ⊆ Y
      hypothesis H₂ : Y ⊆ Z

      private definition ιXY : X => Y := ι X Y H₁
      private definition ιYZ : Y => Z := ι Y Z H₂
      private definition ιXZ : X => Z := ι X Z (subset_trans H₁ H₂)

      example : ιYZ ∘ ιXY = ιXZ :=
        fun_eq_intro
          (take x : Mem X,
            show ιYZ (ιXY x) = ιXZ x, from rfl)
    end part_1

    section part_2
      parameters {A B : Set} {f : A => B}

      private definition ιAA : A => A := ι A A subset_rfl
      private definition ιBB : B => B := ι B B subset_rfl

      example : f = f ∘ ιAA :=
        fun_eq_intro
          (take a : Mem A,
            show f a = f (ιAA a), from eta_red a ▸ rfl)

      example : f = ι B B subset_rfl ∘ f :=
        fun_eq_intro
          (take a : Mem A,
            show f a = ιBB (f a), from eta_exp (f a))

      hypothesis Hf : bijective f

      private noncomputable definition fi : B => A := the_inverse Hf
      private proposition Hfi : f <~> fi := the_inverse_spec Hf

      example : fi ∘ f = ιAA :=
        fun_eq_intro
          (take a : Mem A,
            show fi (f a) = ιAA a, from calc
              fi (f a) = a : fun_eq_elim (and.left Hfi) a
              ... = ιAA a : eta_exp a)

      example : f ∘ fi = ιBB :=
        fun_eq_intro
          (take b : Mem B,
            show f (fi b) = ιBB b, from calc
              f (fi b) = b : fun_eq_elim (and.right Hfi) b
              ... = ιBB b : eta_exp b)
    end part_2

    section part_3
      parameters {X Y Z : Set} {f : X => Z} {g : Y => Z}
      hypothesis Hd : X ∩ Y = ∅

      private proposition Hx : X ⊆ X ∪ Y := subset_union_left
      private proposition Hy : Y ⊆ X ∪ Y := subset_union_right

      private definition ιX : X => X ∪ Y := ι X (X ∪ Y) Hx
      private definition ιY : Y => X ∪ Y := ι Y (X ∪ Y) Hy

      private definition p (h : X ∪ Y => Z) : Prop :=
        h ∘ ιX = f ∧ h ∘ ιY = g

      example : ∃! h : X ∪ Y => Z, p h :=
        let h (a : Mem (X ∪ Y)) : Mem Z :=
          if H : a.1 ∈ X
            then f (Mem.mk H)
            else g (Mem.mk (in_union_right a.2 H))
        in
        have H₁ : h ∘ ιX = f, from fun_eq_intro
          (take x : Mem X,
            show h (ιX x) = f x, from calc
              h (ιX x) = h (Mem.mk (Hx x.2)) : rfl
              ... = f (Mem.mk x.2) : dif_pos x.2
              ... = f x : {eta_red x}),
        have H₂ : h ∘ ιY = g, from fun_eq_intro
          (take y : Mem Y,
            have y.1 ∉ X, from not_in_disjoint_left Hd y.2,
            show h (ιY y) = g y, from calc
              h (ιY y) = h (Mem.mk (Hy y.2)) : rfl
              ... = g (Mem.mk y.2) : dif_neg this
              ... = g y : {eta_red y}),
        have ∀ h' : X ∪ Y => Z, p h' → h' = h, from
        proof
          take h' : X ∪ Y => Z,
          assume Hp : p h',
          show h' = h, from fun_eq_intro
            (take a : Mem (X ∪ Y),
              show h' a = h a, from or.elim a.2
                (suppose a.1 ∈ X,
                  let ax : Mem X := Mem.mk this in
                  have a = ιX ax, from eta_exp a,
                  show h' a = h a, from calc
                    h' a = h' (ιX ax) : {this}
                    ... = f ax : fun_eq_elim (and.left Hp) ax
                    ... = h (ιX ax) : fun_eq_elim H₁⁻¹ ax
                    ... = h a : {this⁻¹})
                (suppose a.1 ∈ Y,
                  let ay : Mem Y := Mem.mk this in
                  have a = ιY ay, from eta_exp a,
                  show h' a = h a, from calc
                    h' a = h' (ιY ay) : {this}
                    ... = g ay : fun_eq_elim (and.right Hp) ay
                    ... = h (ιY ay) : fun_eq_elim H₂⁻¹ ay
                    ... = h a : {this⁻¹}))
        qed,
        show ∃! h : X ∪ Y => Z, p h, from
          exists_unique.intro h (and.intro H₁ H₂) this
    end part_3
  end inclusion

  -- Definition 3.4.1: Images of sets
  definition image {X Y : Set} (f : X => Y) {S : Set} (H : S ⊆ X) : Set :=
    λ y, y ∈ Y ∧ ∃ x : Mem X, y = (f x).1

  -- An image is a subset of the range
  proposition image_spec {X Y : Set} (f : X => Y) {S : Set} (H : S ⊆ X) :
      image f H ⊆ Y :=
    take y,
    suppose y ∈ image f H,
    show y ∈ Y, from and.left this

  -- Definition 3.4.2: Inverse images
  definition preimage {X Y : Set} (f : X => Y) {U : Set} (H : U ⊆ Y) : Set :=
    λ x, x ∈ X ∧ ∀ Hx : x ∈ X, (f (Mem.mk Hx)).1 ∈ U

  -- A preimage is a subset of the domain
  proposition preimage_spec {X Y : Set} (f : X => Y) {U : Set} (H : U ⊆ Y) :
      preimage f H ⊆ X :=
    take x,
    suppose x ∈ preimage f H,
    show x ∈ X, from and.left this

  -- Axiom 3.10: Power set axiom
  definition power_set {X Y : Set} : set (X => Y) := λ f, true

  -- Lemma 3.4.8
  example {X : Set} : set Set := λ s, s ⊆ X

  -- Axiom 3.11: Union
  -/

end object
end set

end chapter_3
