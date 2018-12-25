import standard
open eq.ops
open nat classical set
check sigma.

  -- Axiom of specification for Mem
  -- section specification
  --   parameters {X : Set} (P : Mem X → Prop)

  --   definition specify_mem : Set :=
  --     λ x, x ∈ X ∧ ∀ Hx : x ∈ X, P (Mem.mk Hx)

  --   definition specify_mem_subset : specify_mem ⊆ X :=
  --     take x,
  --     suppose x ∈ specify_mem,
  --     show x ∈ X, from and.left this
  -- end specification
check trivial
find_decl (_ → (_ → _))
