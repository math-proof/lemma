import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[count_of_weight_faultfree_height2_one_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 1 = 1 := by
-- proof
  unfold WeightedSet.countOfWeight
  have hset : {a | FaultfreeTilingsHeight2.weight a = 1} = {⟨1, faultfreeTiling_1_2⟩} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact faultfreeTilingsHeight2_weight1_unique x hx
    · intro hx
      subst hx
      rfl
  have hfin : ({⟨1, faultfreeTiling_1_2⟩} : Set (Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T})).Finite :=
    Set.finite_singleton _
  have heq : (faultfreeTilingsHeight2_isFiniteType 1).toFinset = hfin.toFinset := by
    apply Set.Finite.toFinset_inj.mpr
    exact hset
  rw [heq]
  simp only [Set.Finite.toFinset_singleton, card_singleton]


-- created on 2026-10-20
