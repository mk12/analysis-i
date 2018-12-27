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

(** *** Restate a hypothesis *)

Tactic Notation "given" constr(H) := idtac.

(** *** Restate the current goal *)

Ltac show G := change G.

(** ** Theorems *)

(** *** Double negation *)

Theorem not_not {p : Prop} (Hp : p) : ~ ~ p.
Proof. intro HNp. contradiction (HNp Hp). Qed.

(** *** Modus tollens *)

Theorem mt {p q : Prop} (Hpq : p → q) (HNq : ¬ q) : ¬ p.
Proof.
  intro Hp.
  contradiction HNq.
  exact (Hpq Hp).
Qed.

(** *** Iff helpers *)

Theorem iff_mp {p q : Prop} (Hpq : p ↔ q) (Hp : p): q.
Proof proj1 Hpq Hp.

Theorem iff_mpr {p q : Prop} (Hpq : p ↔ q) (Hq : q): p.
Proof proj2 Hpq Hq.

Theorem iff_mt {p q : Prop} (Hpq : p ↔ q) (HNp : ¬ p) : ¬ q.
Proof mt (proj2 Hpq) HNp.

Theorem iff_mtr {p q : Prop} (Hpq : p ↔ q) (HNq : ¬ q) : ¬ p.
Proof mt (proj1 Hpq) HNq.
