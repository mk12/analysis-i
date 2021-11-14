(******************************************************************************)
(* Copyright 2020 Mitchell Kember. Subject to the MIT License.                *)
(* Formalization of Analysis I: Chapter 3                                     *)
(******************************************************************************)

(** * Chapter 3: Set theory *)

Require Import Common.

(** ** Section 3.1: Fundamentals *)

(** *** Definition 3.1.1: A set is an unordered collection of objects *)

Definition set_of (α : Type) : Type := α → Prop.

(** To satisfy typing, we assume an unspecified universe of objects: *)

Parameter (Object : Set).

Definition set := set_of Object.

(** Set membership: *)

Definition mem {α : Type} (x : α) (A : set_of α) : Prop := A x.

Infix "∈" := mem (at level 70, no associativity).

(** *** Axiom 3.1: Sets are objects *)

Goal _ ∀ (A : set) (B : set_of set), Prop.
Proof. (intros). exact (A ∈ B). Qed.

(** *** Definition 3.1.4: Equality of sets *)

(*
Theorem set_eq {A B : set} : A = B ↔ (∀ x, x ∈ A ↔ x ∈ B).
Proof.
  split.
  - show (A = B → (∀ x, x ∈ A ↔ x ∈ B)).
    intros HEQ x. now rewrite HEQ.
  - show ((∀ x, x ∈ A ↔ x ∈ B) → A = B).
    intro H.
    admit.
Qed.
*)

(** ** Section 3.2: Russell's paradox *)

(** ** Section 3.3: Functions *)

(** ** Section 3.4: Images and inverse images *)

(** ** Section 3.5: Cartesian products *)

(** ** Section 3.6: Cardinality of sets *)
