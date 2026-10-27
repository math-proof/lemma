import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[weight_gen_fun_faultfree_height2_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  FaultfreeTilingsHeight2.weightGenFun (R := ℚ) faultfreeTilingsHeight2_isFiniteType =
    PowerSeries.X + PowerSeries.X ^ 2 := by
-- proof
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk, map_add, coeff_X, coeff_X_pow]
  rcases n with _ | _ | _ | n
  · -- n = 0
    have h0 : FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 0 = 0 :=
      countOfWeight_faultfreeHeight2_eq_zero 0 (by omega) (by omega)
    simp [h0]
  · -- n = 1
    rw [countOfWeight_faultfreeHeight2_one]
    norm_num
  · -- n = 2
    rw [countOfWeight_faultfreeHeight2_two]
    norm_num
  · -- n ≥ 3
    have hn1 : n + 3 ≠ 1 := by omega
    have hn2 : n + 3 ≠ 2 := by omega
    have h3 : FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType (n + 3) = 0 :=
      countOfWeight_faultfreeHeight2_eq_zero (n + 3) hn1 hn2
    simp [h3, hn2]


-- created on 2026-10-20
