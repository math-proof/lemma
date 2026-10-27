import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part4
open scoped BigOperators


/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private lemma sublevelSet_finite
-- given
  (S : NonnegativeDiscreteSpectrum)
  (Λ : ℝ) :
-- imply
  (S.sublevelSet Λ).Finite := by
-- proof
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp S.tendsto_eigenvalue_atTop Λ
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range N)) fun j hj => ?_
  simp only [NonnegativeDiscreteSpectrum.sublevelSet, Set.mem_ofPred_eq] at hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have hle : N ≤ j := not_lt.mp h
  exact (not_le.mpr hj) (hN j hle)

-- created on 2026-10-10
-- updated on 2026-10-26
