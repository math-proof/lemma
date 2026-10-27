import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.NumberTheoryI.code.CDVRExtensions
open NormedSpaceNorm FiniteDimensionalNormTopology AbsoluteValueExtension ValuationFormula


namespace NormedSpaceNorm

/--
[nullity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma nullity
  [NontriviallyNormedField K]
  {v : V} :
-- imply
  ‖v‖ = 0 ↔ v = 0 :=
-- proof
  norm_eq_zero
end NormedSpaceNorm
namespace SupNorm


namespace FiniteDimensionalNormTopology

/--
[complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma complete
  {K : Type*}
  [NontriviallyNormedField K]
  [CompleteSpace K]
  {V : Type*}
  [NormedAddCommGroup V]
  [NormedSpace K V]
  [FiniteDimensional K V] :
-- imply
  CompleteSpace V :=
-- proof
  FiniteDimensional.complete K V

end FiniteDimensionalNormTopology

namespace FiniteDimensionalNormTopology

/--
[linear_map_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma linear_map_continuous
  {K : Type*}
  [NontriviallyNormedField K]
  [CompleteSpace K]
  [AddCommGroup E]
  [Module K E]
  [TopologicalSpace E]
  [IsTopologicalAddGroup E]
  [ContinuousSMul K E]
  [T2Space E]
  [FiniteDimensional K E]
  [AddCommGroup F]
  [Module K F]
  [TopologicalSpace F]
  [IsTopologicalAddGroup F]
  [ContinuousSMul K F]
  {f : E →ₗ[K] F} :
-- imply
  Continuous f :=
-- proof
  LinearMap.continuous_of_finiteDimensional f

end FiniteDimensionalNormTopology

namespace FiniteDimensionalNormTopology

/--
[completeSpace_and_continuous_linearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma completeSpace_and_continuous_linearMap
  {K : Type*}
  [NontriviallyNormedField K]
  [CompleteSpace K] :
-- imply
  (∀ (V : Type*) [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V], CompleteSpace V) ∧ (∀ {E : Type*} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E] [FiniteDimensional K E] {F : Type*} [AddCommGroup F] [Module K F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul K F] (f : E →ₗ[K] F), Continuous f) :=
-- proof
  ⟨fun V => complete K V, fun f => linear_map_continuous K f⟩

end FiniteDimensionalNormTopology

/--
[integralClosure_completeDVR_isDVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma integralClosure_completeDVR_isDVR
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra A B]
  [Algebra B L]
  [IsScalarTower A B L]
  [IsIntegralClosure B A L] :
-- imply
  IsDiscreteValuationRing B :=
-- proof
  integral_closure_complete_DVR_is_DVR A K L B
namespace AbsoluteValueExtension
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

namespace AbsoluteValueExtension

/--
[spectralNorm_extends_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma spectralNorm_extends_norm
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {k : K} :
-- imply
  spectralNorm K L (algebraMap K L k) = ‖k‖ :=
-- proof
  spectralNorm_extends k

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[spectralNorm_unique_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma spectralNorm_unique_extension
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {f : AbsoluteValue L ℝ}
  {x : L}
-- given
  (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖) :
-- imply
  f x = spectralNorm K L x :=
-- proof
  spectralNorm_unique_field_norm_ext hf_ext x

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[finiteExtension_completeSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma finiteExtension_completeSpace
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L] :
-- imply
  @CompleteSpace L (spectralNorm.uniformSpace K L) :=
-- proof
  spectralNorm.completeSpace K L

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[spectralNorm_le_one_iff_minpoly_coeff_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma spectralNorm_le_one_iff_minpoly_coeff_norm_le_one
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {x : L} :
-- imply
  spectralNorm K L x ≤ 1 ↔ ∀ (i : ℕ), ‖(minpoly K x).coeff i‖ ≤ 1 := by
-- proof
  have hx_int : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  exact spectralValue_le_one_iff (minpoly.monic hx_int)

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[integralClosure_isDVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma integralClosure_isDVR
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Algebra A K]
  [IsFractionRing A K]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra A B]
  [Algebra B L]
  [IsScalarTower A B L]
  [IsIntegralClosure B A L] :
-- imply
  IsDiscreteValuationRing B :=
-- proof
  integralClosure_completeDVR_isDVR A K L B

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[norm_algebraMap_unit_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma norm_algebraMap_unit_eq_one
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [CommRing R]
  [IsDomain R]
  [NormedField F]
  [Algebra R F]
  [IsFractionRing R F]
  {x : R}
-- given
  (hbdd : ∀ r : R, ‖algebraMap R F r‖ ≤ 1)
  (hu : IsUnit x) :
-- imply
  ‖algebraMap R F x‖ = 1 := by
-- proof
  obtain ⟨u, rfl⟩ := hu
  have h1 := hbdd (u : R)
  have h2 := hbdd (↑u⁻¹ : R)
  have h3 : ‖algebraMap R F (u : R)‖ * ‖algebraMap R F (↑u⁻¹ : R)‖ = 1 := by
    rw [← norm_mul, ← map_mul]; simp [Units.mul_inv]
  by_contra hne
  linarith [lt_of_le_of_ne h1 hne,
    mul_le_mul_of_nonneg_left h2 (norm_nonneg (algebraMap R F (u : R)))]

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[dvd_pow_of_norm_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma dvd_pow_of_norm_le_pow
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  [NormedField F]
  [Algebra R F]
  [IsFractionRing R F]
  {π : R}
  {x : R}
  {n : ℕ}
-- given
  (hbdd : ∀ r : R, ‖algebraMap R F r‖ ≤ 1)
  (hnu : ∀ r : R, ¬IsUnit r → ‖algebraMap R F r‖ < 1)
  (hπ : Irreducible π)
  (hx : ‖algebraMap R F x‖ ≤ ‖algebraMap R F π‖ ^ n) :
-- imply
  π ^ n ∣ x := by
-- proof
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hπ_lt : ‖algebraMap R F π‖ < 1 := hnu π hπ.1
    have hπ_pos : 0 < ‖algebraMap R F π‖ := by
      rw [norm_pos_iff]
      exact fun h0 => hπ.ne_zero ((IsFractionRing.injective R F) (by rwa [map_zero]))
    have hx_lt : ‖algebraMap R F x‖ < 1 := calc
      ‖algebraMap R F x‖ ≤ ‖algebraMap R F π‖ ^ (n + 1) := hx
      _ ≤ ‖algebraMap R F π‖ ^ 1 :=
        pow_le_pow_of_le_one hπ_pos.le hπ_lt.le (by omega)
      _ < 1 := by rwa [pow_one]
    have hx_nonunit : ¬IsUnit x := fun hu =>
      absurd (norm_algebraMap_unit_eq_one hbdd hu ▸ hx_lt) (not_lt.mpr le_rfl)
    obtain ⟨c, hc⟩ : π ∣ x := by
      have hmem : x ∈ IsLocalRing.maximalIdeal R := by
        by_contra h; exact hx_nonunit (IsLocalRing.notMem_maximalIdeal.mp h)
      rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    rw [hc, pow_succ, mul_comm (π ^ n) π]
    exact mul_dvd_mul_left π (ih c (by
      rw [hc, map_mul, norm_mul] at hx; rw [pow_succ] at hx
      nlinarith [mul_comm (‖algebraMap R F π‖ ^ n) (‖algebraMap R F π‖)]))

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[isPrecomplete_maximalIdeal_of_completeSpace_fractionField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma isPrecomplete_maximalIdeal_of_completeSpace_fractionField
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {F : Type*}
  [NormedField F]
  [CompleteSpace F]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  [Algebra R F]
  [IsFractionRing R F]
-- given
  (hbdd : ∀ r : R, ‖algebraMap R F r‖ ≤ 1)
  (hnu : ∀ r : R, ¬IsUnit r → ‖algebraMap R F r‖ < 1)
  (hbdd_surj : ∀ x : F, ‖x‖ ≤ 1 → ∃ r : R, algebraMap R F r = x) :
-- imply
  IsPrecomplete (IsLocalRing.maximalIdeal R) R := by
-- proof
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ_lt : ‖algebraMap R F π‖ < 1 := hnu π hπ.1
  constructor
  intro f hf
  set g : ℕ → F := fun n => algebraMap R F (f n)
  have hdiff : ∀ {m n : ℕ}, m ≤ n → ‖g m - g n‖ ≤ ‖algebraMap R F π‖ ^ m := by
    intro m n hmn
    simp only [g, ← map_sub]
    have hmem : f m - f n ∈ (IsLocalRing.maximalIdeal R) ^ m := by
      have := SModEq.sub_mem.mp (hf hmn); simpa using this
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    rw [hc, map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hbdd c)
  have hcauchy : CauchySeq g := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hπ_lt
    exact ⟨N, fun n hn => by
      rw [dist_eq_norm, norm_sub_rev]; exact lt_of_le_of_lt (hdiff hn) hN⟩
  obtain ⟨L', hL'⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hL'_bdd : ‖L'‖ ≤ 1 :=
    le_of_tendsto hL'.norm (Filter.Eventually.of_forall (fun n => hbdd (f n)))
  obtain ⟨L, hL⟩ := hbdd_surj L' hL'_bdd
  have hconv_rate : ∀ n, ‖g n - L'‖ ≤ ‖algebraMap R F π‖ ^ n := fun n =>
    le_of_tendsto (tendsto_const_nhds.sub hL').norm
      (Filter.eventually_atTop.mpr ⟨n, fun k hk => hdiff hk⟩)
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem]
  suffices f n - L ∈ (IsLocalRing.maximalIdeal R) ^ n by simpa
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact dvd_pow_of_norm_le_pow hbdd hnu hπ (f n - L) n (by
    simp only [map_sub, hL]; exact hconv_rate n)

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[spectralNorm_extension_exists_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma spectralNorm_extension_exists_unique
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L] :
-- imply
  (∀ (k : K), spectralNorm K L (algebraMap K L k) = ‖k‖) ∧ (∀ (f : AbsoluteValue L ℝ) (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖) (x : L), f x = spectralNorm K L x) :=
-- proof
  ⟨spectralNorm_extends_norm K L, spectralNorm_unique_extension K L⟩

end AbsoluteValueExtension

namespace AbsoluteValueExtension

/--
[finiteExtension_complete_and_valuation_ring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma finiteExtension_complete_and_valuation_ring
  {K : Type*}
  [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L] :
-- imply
  @CompleteSpace L (spectralNorm.uniformSpace K L) ∧ (∀ (x : L), spectralNorm K L x ≤ 1 ↔ ∀ (i : ℕ), ‖(minpoly K x).coeff i‖ ≤ 1) :=
-- proof
  ⟨finiteExtension_completeSpace K L, spectralNorm_le_one_iff_minpoly_coeff_norm_le_one K L⟩
end AbsoluteValueExtension
namespace ValuationFormula

end AbsoluteValueExtension

namespace ValuationFormula

/--
[val_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma val_one
  [Field L]
  {v : L → ℤ}
-- given
  (hv : ∀ a b : L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b) :
-- imply
  v 1 = 0 := by
-- proof
  have h := hv 1 1 one_ne_zero one_ne_zero; simp at h; linarith

end ValuationFormula

namespace ValuationFormula

/--
[val_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma val_inv
  [Field L]
  {v : L → ℤ}
  {a : L}
-- given
  (hv : ∀ a b : L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)
  (ha : a ≠ 0) :
-- imply
  v a⁻¹ = -v a := by
-- proof
  have h := hv a a⁻¹ ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha] at h
  linarith [val_one v hv]

end ValuationFormula

namespace ValuationFormula

/--
[val_pow_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma val_pow_nat
  [Field L]
  {v : L → ℤ}
  {a : L}
  {n : ℕ}
-- given
  (hv : ∀ a b : L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)
  (ha : a ≠ 0) :
-- imply
  v (a ^ n) = (n : ℤ) * v a := by
-- proof
  induction n with
  | zero => simp [val_one v hv]
  | succ n ih =>
    rw [pow_succ, hv _ _ (pow_ne_zero _ ha) ha, ih]
    push_cast; ring

end ValuationFormula

namespace ValuationFormula

/--
[val_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma val_zpow
  [Field L]
  {v : L → ℤ}
  {a : L}
  {n : ℤ}
-- given
  (hv : ∀ a b : L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)
  (ha : a ≠ 0) :
-- imply
  v (a ^ n) = n * v a := by
-- proof
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact val_pow_nat v hv a ha n
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [val_inv v hv _ (pow_ne_zero _ ha), val_pow_nat v hv a ha]
    simp [Int.negSucc_eq]; ring

end ValuationFormula

namespace ValuationFormula

/--
[norm_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma norm_zpow
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {x : L}
  {n : ℤ} :
-- imply
  Algebra.norm K (x ^ n) = (Algebra.norm K x) ^ n := by
-- proof
  cases n with
  | ofNat n => simp [zpow_natCast, map_pow]
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [Algebra.norm_inv, map_pow]

end ValuationFormula

namespace ValuationFormula

/--
[dvr_norm_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma dvr_norm_decomp
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {v_K : K → ℤ}
  {v_L : L → ℤ}
  {π_L : L}
  {x : L}
-- given
  (hv_K : ∀ a b : K, a ≠ 0 → b ≠ 0 → v_K (a * b) = v_K a + v_K b)
  (hv_L : ∀ a b : L, a ≠ 0 → b ≠ 0 → v_L (a * b) = v_L a + v_L b)
  (hπ_L : π_L ≠ 0)
  (hπ_L_val : v_L π_L = 1)
  (hx : x ≠ 0) :
-- imply
  ∃ (u : L), u ≠ 0 ∧ v_L u = 0 ∧ v_K (Algebra.norm K x) = v_K (Algebra.norm K u) + v_L x * v_K (Algebra.norm K π_L) := by
-- proof
  set n := v_L x with hn_def
  set u := x * (π_L ^ n)⁻¹ with hu_def
  have hu_ne : u ≠ 0 := mul_ne_zero hx (inv_ne_zero (zpow_ne_zero _ hπ_L))
  refine ⟨u, hu_ne, ?_, ?_⟩
  ·
    rw [hu_def, hv_L _ _ hx (inv_ne_zero (zpow_ne_zero _ hπ_L))]
    rw [val_inv v_L hv_L _ (zpow_ne_zero _ hπ_L)]
    rw [val_zpow v_L hv_L π_L hπ_L n, hπ_L_val]
    ring
  ·
    have hx_eq : x = u * π_L ^ n := by
      rw [hu_def, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hπ_L), mul_one]
    rw [hx_eq, map_mul (Algebra.norm K), norm_zpow]
    have hNu_ne : Algebra.norm K u ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]; exact hu_ne
    have hNπ_pow_ne : (Algebra.norm K π_L) ^ n ≠ 0 :=
      zpow_ne_zero _ (by rw [Ne, Algebra.norm_eq_zero_iff]; exact hπ_L)
    rw [hv_K _ _ hNu_ne hNπ_pow_ne]
    congr 1
    exact val_zpow v_K hv_K _ (by rw [Ne, Algebra.norm_eq_zero_iff]; exact hπ_L) n

end ValuationFormula

namespace ValuationFormula

/--
[norm_valuation_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma norm_valuation_identity
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {v_K : K → ℤ}
  {v_L : L → ℤ}
  {π_L : L}
  {f_q : ℕ}
  {x : L}
-- given
  (hv_K : ∀ a b : K, a ≠ 0 → b ≠ 0 → v_K (a * b) = v_K a + v_K b)
  (hv_L : ∀ a b : L, a ≠ 0 → b ≠ 0 → v_L (a * b) = v_L a + v_L b)
  (_hf_q : 0 < f_q)
  (hπ_L : π_L ≠ 0)
  (hπ_L_val : v_L π_L = 1)
  (h_unif_norm : v_K (Algebra.norm K π_L) = (f_q : ℤ))
  (h_unit_norm : ∀ u : L, u ≠ 0 → v_L u = 0 → v_K (Algebra.norm K u) = 0)
  (hx : x ≠ 0) :
-- imply
  v_K (Algebra.norm K x) = (f_q : ℤ) * v_L x := by
-- proof
  obtain ⟨u, hu_ne, hu_unit, h_decomp⟩ :=
    dvr_norm_decomp v_K v_L π_L hv_K hv_L hπ_L hπ_L_val x hx
  rw [h_decomp]
  rw [h_unit_norm u hu_ne hu_unit]
  rw [h_unif_norm]
  ring

end ValuationFormula

namespace ValuationFormula

/--
[valuation_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma valuation_formula
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {v_K : K → ℤ}
  {v_L : L → ℤ}
  {π_L : L}
  {f_q : ℕ}
  {x : L}
-- given
  (hv_K : ∀ a b : K, a ≠ 0 → b ≠ 0 → v_K (a * b) = v_K a + v_K b)
  (hv_L : ∀ a b : L, a ≠ 0 → b ≠ 0 → v_L (a * b) = v_L a + v_L b)
  (hf_q : 0 < f_q)
  (hπ_L : π_L ≠ 0)
  (hπ_L_val : v_L π_L = 1)
  (h_unif_norm : v_K (Algebra.norm K π_L) = (f_q : ℤ))
  (h_unit_norm : ∀ u : L, u ≠ 0 → v_L u = 0 → v_K (Algebra.norm K u) = 0)
  (hx : x ≠ 0) :
-- imply
  (v_L x : ℚ) = (1 : ℚ) / (f_q : ℚ) * (v_K (Algebra.norm K x) : ℚ) := by
-- proof
  have h_identity :=
    norm_valuation_identity v_K v_L π_L f_q hv_K hv_L hf_q hπ_L hπ_L_val
      h_unif_norm h_unit_norm x hx
  have hfq_ne : (f_q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hf_q)
  rw [h_identity]
  push_cast
  field_simp

end ValuationFormula

/--
[valuation_eq_inv_residueDeg_mul_norm_valuation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean)
-/
@[path]
lemma valuation_eq_inv_residueDeg_mul_norm_valuation
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  {v_K : K → ℤ}
  {v_L : L → ℤ}
  {π_L : L}
  {f_q : ℕ}
  {x : L}
-- given
  (hv_K : ∀ a b : K, a ≠ 0 → b ≠ 0 → v_K (a * b) = v_K a + v_K b)
  (hv_L : ∀ a b : L, a ≠ 0 → b ≠ 0 → v_L (a * b) = v_L a + v_L b)
  (hf_q : 0 < f_q)
  (hπ_L : π_L ≠ 0)
  (hπ_L_val : v_L π_L = 1)
  (h_unif_norm : v_K (Algebra.norm K π_L) = (f_q : ℤ))
  (h_unit_norm : ∀ u : L, u ≠ 0 → v_L u = 0 → v_K (Algebra.norm K u) = 0)
  (hx : x ≠ 0) :
-- imply
  (v_L x : ℚ) = (1 : ℚ) / (f_q : ℚ) * (v_K (Algebra.norm K x) : ℚ) :=
-- proof
  ValuationFormula.valuation_formula v_K v_L π_L f_q hv_K hv_L hf_q hπ_L hπ_L_val
    h_unif_norm h_unit_norm x hx
end


-- created on 2026-10-23
