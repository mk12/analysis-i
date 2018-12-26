(******************************************************************************)
(* Copyright 2018 Mitchell Kember. Subject to the MIT License.                *)
(* Formalization of Analysis I: Common theorems                               *)
(******************************************************************************)

(* Require Export Coq.Logic.Classical. *)
Require Export Coq.Setoids.Setoid.
Require Export Coq.Unicode.Utf8.

(** Restate the current goal *)
Ltac show G := tryif change G then idtac else fail 0 "Not the current goal".

(** Modus tollens *)
Theorem mt {p q : Prop} (Hpq : p → q) (Hnq : ¬ q) : ¬ p.
Proof.
  intro Hp.
  contradiction Hnq.
  exact (Hpq Hp).
Qed.
