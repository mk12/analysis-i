(******************************************************************************)
(* Copyright 2018 Mitchell Kember. Subject to the MIT License.                *)
(* Formalization of Analysis I: Common theorems                               *)
(******************************************************************************)

Require Export Coq.Unicode.Utf8.
(* Require Export Coq.Logic.Classical. *)

(** Restate the current goal *)
Ltac show G := change G.

(** Modus tollens *)
Theorem mt {p q : Prop} (Hpq : p → q) (Hnq : ¬ q) : ¬ p.
Proof.
  intro Hp.
  absurd q.
  - exact Hnq.
  - exact (Hpq Hp).
Qed.
