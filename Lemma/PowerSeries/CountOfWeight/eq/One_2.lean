import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[count_of_weight_faultfree_height2_two_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 2 = 1 := by
-- proof
  unfold WeightedSet.countOfWeight
  -- The set of faultfree tilings of weight 2 is a singleton
  have hsingleton : {a : Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T} |
      FaultfreeTilingsHeight2.weight a = 2} =
      {⟨2, twoHorizontalDominos, twoHorizontalDominos_isFaultfree⟩} := by
    ext ⟨n, T, hT⟩
    simp only [FaultfreeTilingsHeight2, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hn
      -- hn : weight ⟨n, T, hT⟩ = 2, i.e. n = 2 after unfolding
      subst hn
      have heq := faultfree_tiling_width2_unique T hT
      subst heq
      rfl
    · intro heq
      simp only [Sigma.mk.inj_iff] at heq
      obtain ⟨hn, hTeq⟩ := heq
      simp only [hn]
  have hfin := faultfreeTilingsHeight2_isFiniteType 2
  have hfin' := Set.finite_singleton (⟨2, twoHorizontalDominos, twoHorizontalDominos_isFaultfree⟩ :
      Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T})
  have heq_fin : hfin.toFinset = hfin'.toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      have : x ∈ {a | FaultfreeTilingsHeight2.weight a = 2} := hx
      rw [hsingleton] at this
      exact this
    · intro hx
      subst hx
      rfl
  rw [heq_fin]
  simp only [Set.Finite.toFinset_singleton, card_singleton]


-- created on 2026-10-20
