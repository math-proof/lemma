import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Problem_2_4
open Finset BigOperators Real


/--
[sum_comp_eq_of_multiset_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Problem_2_4.lean)
-/
@[path]
lemma sum_comp_eq_of_multiset_map_eq
  {d : ℕ}
  {a b : Fin d → ℝ}
  {f : ℝ → ℝ}
-- given
  (h : Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val) :
-- imply
  ∑ i, f (a i) = ∑ i, f (b i) := by
-- proof
  have : Multiset.map f (Multiset.map a univ.val) =
    Multiset.map f (Multiset.map b univ.val) := by rw [h]
  rw [Multiset.map_map, Multiset.map_map] at this
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact congr_arg Multiset.sum this


-- created on 2026-10-23
