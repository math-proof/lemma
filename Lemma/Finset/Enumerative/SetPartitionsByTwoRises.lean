import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.SetPartitionsByTwoRises
open scoped BigOperators
open MetaMathlibExt


/--
[setPartition_twoRise_ordinaryGeneratingFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SetPartitionsByTwoRises.lean)
-/
@[path]
private lemma setPartition_twoRise_ordinaryGeneratingFunction_eq
  {k : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  let x : MvPowerSeries (Fin 2) ℚ := by
-- proof
  apply MetaMathlibExt.setPartition_twoRise_ordinaryGeneratingFunction k hk


-- created on 2026-10-20
