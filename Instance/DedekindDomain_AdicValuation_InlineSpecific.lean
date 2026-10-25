-- Carved from Lemma/Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean: instance decls only.
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Path
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.RingTheory.Valuation.Discrete.RankOne
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

section

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

private instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
  exists_countable_dense :=
    ⟨_, Set.countable_range _, HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)⟩


end IsDedekindDomain.HeightOneSpectrum

end


section

namespace IsDedekindDomain.HeightOneSpectrum


variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)


instance : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

open Valuation.IsRankOneDiscrete in


instance : (v.completionIdeal K).LiesOver v.asIdeal := ⟨by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]⟩

open IsLocalRing in


namespace adicCompletion

open scoped algebraMap in


instance : Ring.DimensionLEOne (v.adicCompletionIntegers K) where
  maximalOfPrime {𝔭} h𝔭_ne_bot h𝔭_prime := by
    let ⟨x, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭_ne_bot
    let ⟨π, hπ⟩ := exists_uniformizer K v
    obtain ⟨n, ⟨u, rfl⟩⟩ := eq_pow_uniformizer_mul_unit K v hx.2 hπ
    simp only [Units.isUnit, Ideal.mul_unit_mem_iff_mem, ne_eq, mul_eq_zero, pow_eq_zero_iff',
      Units.ne_zero, or_false, not_and, Decidable.not_not] at hx
    by_cases hn : n = 0
    · simp only [hn, pow_zero, ← 𝔭.eq_top_iff_one, implies_true, and_true] at hx
      exact h𝔭_prime.ne_top hx |>.elim
    · rw [h𝔭_prime.pow_mem_iff_mem n (by omega), ← 𝔭.span_singleton_le_iff_mem,
        ← maximalIdeal_eq_span_uniformizer K v hπ] at hx
      exact IsLocalRing.maximalIdeal_le h𝔭_prime.ne_top hx.1

open scoped algebraMap in
instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  apply IsPrincipalIdealRing.of_prime
  intro P hP
  by_cases hP_bot : P = ⊥
  · exact hP_bot ▸ bot_isPrincipal
  · let ⟨π, hπ⟩ := exists_uniformizer K v
    use π
    rw [IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_bot)]
    exact maximalIdeal_eq_span_uniformizer K v hπ

instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    let ⟨π, hπ⟩ := exists_uniformizer K v
    rw [maximalIdeal_eq_span_uniformizer K v hπ]
    intro h
    simp only [Ideal.span_singleton_eq_bot] at h
    exact uniformizer_ne_zero hπ h

open scoped Valued in
instance : IsDiscreteValuationRing (𝒪[v.adicCompletion K]) :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))


end adicCompletion


end IsDedekindDomain.HeightOneSpectrum

end
