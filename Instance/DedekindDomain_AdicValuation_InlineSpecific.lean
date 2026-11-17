-- Carved from Lemma/Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean: instance decls only.

module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.Topology.Path
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Abbrev.DedekindDomain_AdicValuation_InlineSpecific

@[expose] public section

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

open scoped WithZero

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

noncomputable instance : ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

private lemma mem_completionIdeal_iff (x : v.adicCompletionIntegers K) :
    x ∈ completionIdeal K v ↔ Valued.v x.val < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

private lemma algebraMap_completionIntegers (x : A) :
    (algebraMap A (v.adicCompletionIntegers K) x) = (algebraMap A (v.adicCompletion K) x) :=
  rfl

instance : (v.completionIdeal K).LiesOver v.asIdeal := ⟨by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]⟩

private theorem maximalIdeal_le_of_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R

namespace adicCompletion

open scoped algebraMap

private theorem exists_uniformizer (v : HeightOneSpectrum A) :
    ∃ π : v.adicCompletionIntegers K, Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  use π
  rw [← WithZero.exp, ← hπ, ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]

variable {K} in
private theorem uniformizer_ne_zero {v : HeightOneSpectrum A}
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    π ≠ 0 := by
  contrapose! hπ
  simp [hπ]

open scoped Multiplicative

variable {K} in
private theorem uniformizer_not_isUnit {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬IsUnit (π : v.adicCompletionIntegers K) := by
  simp only [adicCompletionIntegers.isUnit_iff_valued_eq_one, hπ, ← WithZero.coe_one,
    WithZero.coe_inj, ← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq]
  decide

set_option maxHeartbeats 4000000 in
private theorem eq_pow_uniformizer_mul_unit {x : v.adicCompletionIntegers K} (hx : x ≠ 0)
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π ^ n * u := by
  have hx' : Valued.v x.1 ≠ 0 := by simp [hx]
  let m := - Multiplicative.toAdd (WithZero.unzero hx')
  have hm₀ : 0 ≤ m := by
    simp_rw [m, Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le]
    rw [← WithZero.coe_le_coe]; exact (WithZero.coe_unzero _).symm ▸ x.2
  have hpow : Valued.v ((π.1 : v.adicCompletion K) ^ (-m) * x.val) = 1 := by
    set vK : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
    calc
      vK ((π.1 : v.adicCompletion K) ^ (-m) * x.val)
          = vK ((π.1 : v.adicCompletion K) ^ (-m)) * vK x.val := vK.map_mul _ _
      _ = (vK π.1) ^ (-m) * vK x.val := by rw [map_zpow₀ vK]
      _ = 1 := by
        rw [hπ, ofAdd_neg, WithZero.coe_inv, inv_zpow', neg_neg, ← WithZero.coe_zpow,
          ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd, WithZero.coe_inv,
          WithZero.coe_unzero, inv_mul_cancel₀ hx']
  let a : v.adicCompletionIntegers K :=
    ⟨(π.1 : v.adicCompletion K) ^ (-m) * x.val, le_of_eq hpow⟩
  refine ⟨m.toNat, (adicCompletionIntegers.isUnit_iff_valued_eq_one (a := a) |>.2 hpow).unit,
    Subtype.ext ?_⟩
  simp only [zpow_neg, IsUnit.unit_spec, MulMemClass.coe_mul, SubmonoidClass.coe_pow, a,
    ← zpow_natCast, m.toNat_of_nonneg hm₀, ← mul_assoc]
  rw [mul_inv_cancel₀ (zpow_ne_zero _ <| (by simp [uniformizer_ne_zero hπ])), one_mul]

open scoped algebraMap in
private theorem maximalIdeal_eq_span_uniformizer {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {(π : v.adicCompletionIntegers K)} := by
  refine (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.span_singleton_ne_top (uniformizer_not_isUnit v hπ)) (fun x hx => ?_)
  by_cases hx₀ : x = 0
  · simp only [hx₀, Ideal.zero_mem]
  · obtain ⟨n, ⟨u, hu⟩⟩ := eq_pow_uniformizer_mul_unit K v hx₀ hπ
    have hn : ¬(IsUnit x) := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
    replace hn : n ≠ 0 := fun h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
    simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self π hn

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
      exact maximalIdeal_le_of_le h𝔭_prime.ne_top hx.1

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
