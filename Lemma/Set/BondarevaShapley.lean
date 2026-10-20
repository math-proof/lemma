import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.BondarevaShapley
open Finset
open MathlibExt.GameTheory.ShapleyValue
open MathlibExt.GameTheory.BondarevaShapleyWanted


/--
[bondareva_shapley](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BondarevaShapley.lean)
-/
@[path]
private lemma bondareva_shapley_eq
  [Fintype Player] [DecidableEq Player]
  {v : CoopGame Player} :
-- imply
  (∃ x : Player → ℝ, IsCoreAllocation v x) ↔ IsBalanced v := by
-- proof
  apply MathlibExt.GameTheory.BondarevaShapleyWanted.bondareva_shapley v


-- created on 2026-10-20
