(******************************************************************************)
(* Copyright 2018 Mitchell Kember. Subject to the MIT License.                *)
(* Formalization of Analysis I: Common theorems                               *)
(******************************************************************************)

Require Export Coq.Setoids.Setoid.
Require Export Coq.Unicode.Utf8.
(* Require Export Coq.Logic.Classical. *)

(** Restate the current goal *)
Ltac show G := tryif change G then idtac else fail 0 "Not the current goal".

(** Superscript -1 for the symmetric equality **)
(* Notation "H ⁻¹" := (eq_sym H) (at level 100, right associativity). *)

(** Modus tollens *)
Theorem mt {p q : Prop} (Hpq : p → q) (Hnq : ¬ q) : ¬ p.
Proof.
  intro Hp.
  absurd q.
  - exact Hnq.
  - exact (Hpq Hp).
Qed.

(** Double negation of eq_refl *)
Theorem nneq {T : Type} {x : T} : ¬ x ≠ x.
Proof. intro. contradiction. Qed.
