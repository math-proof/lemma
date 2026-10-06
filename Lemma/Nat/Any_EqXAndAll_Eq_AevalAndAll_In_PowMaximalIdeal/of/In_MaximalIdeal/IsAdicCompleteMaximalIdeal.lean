import Mathlib
import sympy.Basic

open IsLocalRing
open scoped PowerSeries.WithPiTopology

/--
[IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal.lean)
-/
@[main]
private lemma main
  {𝒪 R : Type u} [CommRing 𝒪] [CommRing R] [IsLocalRing R] [Algebra 𝒪 R]
  {t : R}
-- given
  (h : IsAdicComplete (maximalIdeal R) R)
  (ht : t ∈ maximalIdeal R) :
-- imply
  ∃ ev : PowerSeries 𝒪 →ₐ[𝒪] R, ev PowerSeries.X = t ∧
      (∀ p : Polynomial 𝒪, ev (p : PowerSeries 𝒪) = Polynomial.aeval t p) ∧
      (∀ (n : ℕ) (F : PowerSeries 𝒪), PowerSeries.X ^ n ∣ F → ev F ∈ maximalIdeal R ^ n) := by
-- proof
  classical
  letI wI : WithIdeal R := ⟨maximalIdeal R⟩
  letI uO : UniformSpace 𝒪 := ⊥
  haveI : DiscreteUniformity 𝒪 := ⟨rfl⟩
  haveI : ContinuousSMul 𝒪 R := DiscreteTopology.instContinuousSMul 𝒪 R
  have hI : IsAdic (maximalIdeal R) := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval t := (PowerSeries.hasEval_def t).mpr (WithIdeal.isTopologicallyNilpotent_of_mem ht)
  refine ⟨PowerSeries.aeval ha, ?_, fun p => PowerSeries.aeval_coe ha p, ?_⟩
  · rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]
  · intro n F hF
    obtain ⟨G, rfl⟩ := hF
    rw [map_mul, map_pow, ← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ht n)


-- created on 2026-10-05
