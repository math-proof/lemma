import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.NumberTheoryI.code.Ch22WeberLFunction
open RayClassField
open scoped NumberField


namespace RayClassField

/--
[RayClassChar.norm_evalIdealC_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22WeberLFunction.lean)
-/
@[path]
lemma RayClassChar.norm_evalIdealC_le_one
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪}
  {𝔞 : FracIdealsCoprime K 𝔪} :
-- imply
  ‖χ.evalIdealC 𝔞‖ ≤ 1 := by
-- proof
  unfold RayClassChar.evalIdealC RayClassChar.evalIdeal
  set g := toRayClass K 𝔪 𝔞
  have hpow : (χ g : ℂˣ) ^ Fintype.card (RayClassGroup K 𝔪) = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  have hpow_c : (χ g : ℂ) ^ Fintype.card (RayClassGroup K 𝔪) = 1 := by
    have := congr_arg Units.val hpow
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    exact this
  have hcard : Fintype.card (RayClassGroup K 𝔪) ≠ 0 := Fintype.card_ne_zero
  linarith [Complex.norm_eq_one_of_pow_eq_one hpow_c hcard]

end RayClassField

namespace RayClassField

/--
[RayClassChar.norm_evalPrime_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22WeberLFunction.lean)
-/
@[path]
lemma RayClassChar.norm_evalPrime_le_one
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪}
  {𝔭 : Prime' K} :
-- imply
  ‖χ.evalPrime 𝔭‖ ≤ 1 := by
-- proof
  simp only [RayClassChar.evalPrime]
  split_ifs with h
  · exact χ.norm_evalIdealC_le_one (primeToFracIdealsCoprime K 𝔪 𝔭 h)
  · simp

end RayClassField

namespace RayClassField

/--
[card_primes_le_card_ideals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22WeberLFunction.lean)
-/
@[path]
lemma card_primes_le_card_ideals
  {K : Type u}
  [Field K]
  [NumberField K]
  {n : ℕ} :
-- imply
  Nat.card {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
-- proof
  Nat.card_le_card_of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

end RayClassField

namespace RayClassField

/--
[ideal_count_rpow_summable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22WeberLFunction.lean)
-/
@[path]
lemma ideal_count_rpow_summable
  {K : Type u}
  [Field K]
  [NumberField K]
  {σ : ℝ}
-- given
  (hσ : 1 < σ) :
-- imply
  Summable (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ (-σ))) := by
-- proof
  have hLS : LSeriesSummable
    (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ : ℂ) := by
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg _ (fun n => Nat.cast_nonneg _) zero_le_one
    · simp; exact hσ
    apply Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ)
      (a := NumberField.dedekindZeta_residue K)
    simp only [Real.rpow_one]
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]; congr 1; norm_cast
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  exact (hLS.norm).of_nonneg_of_le (fun n => by positivity) (fun n => by
    rw [LSeries.norm_term_eq]; split_ifs with h
    · subst h
      simp [Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < σ)))]
    · rw [Complex.norm_natCast, Complex.ofReal_re, div_eq_mul_inv,
      ← Real.rpow_neg (Nat.cast_nonneg n)])
set_option maxHeartbeats 400000 in

end RayClassField

namespace RayClassField

/--
[summable_primeIdeal_absNorm_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22WeberLFunction.lean)
-/
@[path]
lemma summable_primeIdeal_absNorm_rpow
  {K : Type u}
  [Field K]
  [NumberField K]
  {σ : ℝ}
-- given
  (hσ : 1 < σ) :
-- imply
  Summable (fun 𝔭 : Prime' K => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-σ)) := by
-- proof
  rw [← (Equiv.sigmaFiberEquiv (fun 𝔭 : Prime' K =>
    Ideal.absNorm 𝔭.asIdeal)).summable_iff]
  suffices h : Summable (fun p : (n : ℕ) × {𝔭 : Prime' K //
    Ideal.absNorm 𝔭.asIdeal = n} => ((p.1 : ℝ) ^ (-σ))) by
    exact h.congr (fun ⟨n, 𝔭, h⟩ => by
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
      congr 1; exact_mod_cast h.symm)
  rw [summable_sigma_of_nonneg (fun ⟨n, _⟩ => by positivity)]
  exact ⟨fun n => Summable.of_finite, by
    simp_rw [tsum_const, nsmul_eq_mul]
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_primes_le_card_ideals K n) (by positivity))
      (ideal_count_rpow_summable K σ hσ)⟩

end RayClassField

namespace RayClassField

/--
[norm_inv_one_sub_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22WeberLFunction.lean)
-/
@[path]
private lemma norm_inv_one_sub_sub_one {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
  ‖(1 - a)⁻¹ - 1‖ ≤ 2 * ‖a‖ := by
  by_cases ha0 : a = 0; · simp [ha0]
  have ha1 : ‖a‖ < 1 := by linarith
  have h1a : (1 : ℂ) - a ≠ 0 := by
    intro h; have := sub_eq_zero.mp h; rw [← this] at ha1; simp at ha1
  rw [show (1 - a)⁻¹ - 1 = a * (1 - a)⁻¹ from by field_simp; ring,
    norm_mul, norm_inv]
  calc ‖a‖ * ‖(1 : ℂ) - a‖⁻¹
    ≤ ‖a‖ * (1 - ‖a‖)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (inv_anti₀ (by linarith)
          (by linarith [norm_sub_norm_le (1 : ℂ) a, norm_one (α := ℂ)]))
        (norm_nonneg a)
    _ ≤ ‖a‖ * (1 / 2)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (inv_anti₀ (by linarith : (0 : ℝ) < 1 / 2) (by linarith)) (norm_nonneg a)
    _ = 2 * ‖a‖ := by ring

end RayClassField


-- created on 2026-10-23
