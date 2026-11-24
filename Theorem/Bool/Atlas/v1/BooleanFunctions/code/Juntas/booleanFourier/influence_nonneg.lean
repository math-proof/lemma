module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.BooleanFunctions.code.Juntas
open BooleanFourier


public section

/--
[influence_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Juntas.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n} :
-- imply
  0 ≤ influence f i := by
-- proof
  unfold influence
  positivity


theorem BooleanFourier.influence_nonneg
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n} :
-- imply
  0 ≤ influence f i := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
