module

public import Mathlib
public import Def.v1.Atlas.AlgebraNotes.code.SymmetricGroups

public section

open Equiv Equiv.Perm SymmetricGroups


/--
[conjugate_iff_same_cycleType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SymmetricGroups.lean)
-/
public theorem Fin.IsConj.is.CycleType
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {σ τ : Perm (Fin n)} :
-- imply
  IsConj σ τ ↔ σ.cycleType = τ.cycleType :=
-- proof
  Equiv.Perm.isConj_iff_cycleType_eq



-- created on 2026-10-23
-- updated on 2026-10-26
