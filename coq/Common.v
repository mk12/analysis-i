(******************************************************************************)
(* Copyright 2018 Mitchell Kember. Subject to the MIT License.                *)
(* Formalization of Analysis I: Common                                        *)
(******************************************************************************)

(** * Common *)

(** ** Flags *)

Export Set Warnings "-notation-overridden".

(** ** Libraries *)

Require Export Coq.Setoids.Setoid.
Require Export Coq.Unicode.Utf8.

(** ** Tactics *)

(** *** Restate the current goal *)

Ltac show G := tryif change G then idtac else fail 0 "Not the current goal".

(** ** Theorems *)

(** *** Modus tollens *)

Theorem mt {p q : Prop} (Hpq : p → q) (HNq : ¬ q) : ¬ p.
Proof.
  intro Hp.
  contradiction HNq.
  exact (Hpq Hp).
Qed.
