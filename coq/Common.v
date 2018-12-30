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

Ltac show G := change G.

(** *** Restate a hypothesis *)

Tactic Notation "given" ne_constr_list(H) := idtac.

(** *** State an intermediate result *)

Tactic Notation "have" uconstr(P) "as" ident(N) "from" uconstr(H) :=
  assert P as N by exact H.

(** ** Theorems *)

(** *** Double negation *)

Theorem not_not {p : Prop} (Hp : p) : ¬ ¬ p.
Proof. intro HNp. contradiction (HNp Hp). Qed.

(** *** Modus tollens *)

Theorem mt {p q : Prop} (Hpq : p → q) (HNq : ¬ q) : ¬ p.
Proof. intro Hp. contradiction (HNq (Hpq Hp)). Qed.

(** *** Iff helpers *)

Theorem iff_mp {p q : Prop} (Hpq : p ↔ q) (Hp : p): q.
Proof proj1 Hpq Hp.

Theorem iff_mpr {p q : Prop} (Hpq : p ↔ q) (Hq : q): p.
Proof proj2 Hpq Hq.

Theorem iff_mt {p q : Prop} (Hpq : p ↔ q) (HNp : ¬ p) : ¬ q.
Proof mt (proj2 Hpq) HNp.

Theorem iff_mtr {p q : Prop} (Hpq : p ↔ q) (HNq : ¬ q) : ¬ p.
Proof mt (proj1 Hpq) HNq.

(** *** De Morgan's laws *)

(* Theorem dm_not_or_not {p q : Prop} (H : ¬ (p ∧ q)) : ¬ p ∨ ¬ q. *)

Theorem dm_not_and {p q : Prop} : ¬ p ∨ ¬ q → ¬ (p ∧ q).
Proof.
  intros [HNp | HNq] [Hp Hq].
  - given (HNp : ¬ p).
    contradiction (HNp Hp).
  - given (HNq : ¬ q).
    contradiction (HNq Hq).
Qed.

(* Theorem dm_not_and_not (H : ¬ (p ∨ q)) : ¬ p ∧ ¬ q. *)

Theorem dm_not_or {p q : Prop} : ¬ p ∧ ¬ q → ¬ (p ∨ q).
  intros [HNp HNq] [Hp | Hq].
  - given (Hp : p).
    contradiction (HNp Hp).
  - given (Hq : q).
    contradiction (HNq Hq).
Qed.
