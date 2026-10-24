import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tilings_finite_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n m : ℕ) :
-- imply
  Set.Finite (Set.univ : Set (Tiling (Rectangle n m))) := by
-- proof
  let f : Tiling (Rectangle n m) → Set Domino := fun T => T.dominos
  have hf : Function.Injective f := by
    intro T₁ T₂ h
    cases T₁; cases T₂
    simp only [f] at h
    congr
  have h_range : Set.range f ⊆ 𝒫 (DominosInRectangle n m) := by
    intro s hs
    simp only [Set.mem_range, f] at hs
    obtain ⟨T, rfl⟩ := hs
    simp only [Set.mem_powerset_iff]
    exact tiling_dominos_subset n m T
  have h_powerset_finite : Set.Finite (𝒫 (DominosInRectangle n m)) := by
    exact (dominosInRectangle_finite n m).powerset
  have h_range_finite : Set.Finite (Set.range f) := by
    exact h_powerset_finite.subset h_range
  have h_univ_finite : Set.Finite (f ⁻¹' Set.range f) := by
    apply h_range_finite.preimage
    exact hf.injOn
  convert h_univ_finite
  ext x
  simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, exists_apply_eq_apply]


-- created on 2026-10-20
