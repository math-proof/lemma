import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[weight_gen_fun_tilings_height2_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  TilingsHeight2.weightGenFun (R := ℚ) tilingsHeight2_isFiniteType =
    PowerSeries.mk fun n => (Nat.fib (n + 1) : ℚ) := by
-- proof
  -- The n-th coefficient of the LHS is countOfWeight n
  -- which equals numTilings n 2 by countOfWeight_tilingsHeight2_eq
  -- which equals Nat.fib (n + 1) by numTilings_2_n
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk]
  rw [countOfWeight_tilingsHeight2_eq, numTilings_2_n]


-- created on 2026-10-20
