import Mathlib
import sympy.Basic
import Def.NumberTheory.NumberField.ArakelovDivisor.Part3
open scoped NumberField nonZeroDivisors
open FractionalIdeal
open NumberField


namespace NumberField

/--
[ArakelovDivisor.sizeHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
lemma ArakelovDivisor.sizeHom_apply
  [Field K] [NumberField K]
  {D : ArakelovDivisor K} :
-- imply
  ArakelovDivisor.sizeHom K D =
    ArakelovDivisor.archHom K D / ArakelovDivisor.idealHom K D :=
-- proof
  rfl

end NumberField

namespace NumberField

/--
[ArakelovDivisor.sizeHom_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
lemma ArakelovDivisor.sizeHom_coe
  [Field K] [NumberField K]
  {D : ArakelovDivisor K} :
-- imply
  (ArakelovDivisor.sizeHom K D : ℝ) =
    (∏ w : InfinitePlace K, (D.2 w : ℝ) ^ w.mult) /
    ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) := by
-- proof
  rw [ArakelovDivisor.sizeHom_apply,
    show (ArakelovDivisor.archHom K) D = ArakelovDivisor.archimedeanFactor K D from rfl,
    show (ArakelovDivisor.idealHom K) D = ArakelovDivisor.idealNorm K D from rfl,
    div_eq_mul_inv, Positive.val_mul, Positive.coe_inv,
    ArakelovDivisor.archimedeanFactor_coe, ArakelovDivisor.idealNorm_coe,
    (div_eq_mul_inv _ _).symm]

end NumberField

namespace NumberField

/--
[ArakelovDivisor.mem_sectionSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
lemma ArakelovDivisor.mem_sectionSet
  [Field K] [NumberField K]
  {D : ArakelovDivisor K}
  {x : K} :
-- imply
  x ∈ D.sectionSet ↔
    x ∈ (D.1 : FractionalIdeal (𝓞 K)⁰ K) ∧
    ∀ w : InfinitePlace K, w x ≤ (D.2 w : ℝ) :=
-- proof
  Iff.rfl

end NumberField

namespace NumberField

/--
[ArakelovDivisor.sectionSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
lemma ArakelovDivisor.sectionSet_finite
  [Field K] [NumberField K]
  {D : ArakelovDivisor K} :
-- imply
  D.sectionSet.Finite := by
-- proof
  obtain ⟨d, hd_mem, hden⟩ := (D.1 : FractionalIdeal (𝓞 K)⁰ K).isFractional
  have hd_ne : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd_mem
  have hc_ne : algebraMap (𝓞 K) K d ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd_ne
  obtain ⟨w₀, hw₀⟩ := Set.exists_upper_bound_image Set.univ
    (fun w : InfinitePlace K => ((D.2 w : ℝ))) Set.finite_univ
  obtain ⟨φ₀, hφ₀⟩ := Set.exists_upper_bound_image Set.univ
    (fun φ : K →+* ℂ => ‖φ (algebraMap (𝓞 K) K d)‖) Set.finite_univ
  refine Set.Finite.of_finite_image (f := fun x => algebraMap (𝓞 K) K d * x)
    ((NumberField.Embeddings.finite_of_norm_le K ℂ
      (‖φ₀ (algebraMap (𝓞 K) K d)‖ * ((D.2 w₀ : ℝ)))).subset ?_)
    (mul_right_injective₀ hc_ne).injOn
  intro y hy
  simp only [Set.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [ArakelovDivisor.mem_sectionSet] at hx
  obtain ⟨hxI, hxb⟩ := hx
  refine ⟨?_, fun φ => ?_⟩
  · obtain ⟨z, hz⟩ := hden x (FractionalIdeal.mem_coe.mpr hxI)
    rw [Algebra.smul_def] at hz
    exact hz ▸ RingOfIntegers.isIntegral_coe z
  · have hφx : ‖φ x‖ ≤ ((D.2 w₀ : ℝ)) := by
    have h1 : (InfinitePlace.mk φ) x = ‖φ x‖ := rfl
    rw [← h1]
    exact le_trans (hxb (InfinitePlace.mk φ)) (hw₀ _ (Set.mem_univ _))
    rw [map_mul, norm_mul]
    exact mul_le_mul (hφ₀ _ (Set.mem_univ _)) hφx (norm_nonneg _) (norm_nonneg _)

end NumberField

namespace NumberField

/--
[coe_principalDivisor_snd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
lemma coe_principalDivisor_snd
  [Field K] [NumberField K]
  {x : Kˣ}
  {w : InfinitePlace K} :
-- imply
  (((principalDivisor K x).2 w : { r : ℝ // 0 < r }) : ℝ) = w (x : K) :=
-- proof
  rfl

end NumberField

namespace NumberField

/--
[coe_principalDivisor_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
lemma coe_principalDivisor_fst
  [Field K] [NumberField K]
  {x : Kˣ} :
-- imply
  ((principalDivisor K x).1 : FractionalIdeal (𝓞 K)⁰ K) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) :=
-- proof
  coe_toPrincipalIdeal x

end NumberField

namespace NumberField

/--
[size_principal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
lemma size_principal
  [Field K] [NumberField K]
  {x : Kˣ} :
-- imply
  ArakelovDivisor.sizeHom K (principalHom K x) = 1 := by
-- proof
  have hmap : principalHom K x = principalDivisor K x := rfl
  rw [hmap]
  apply Subtype.ext
  show ((ArakelovDivisor.sizeHom K (principalDivisor K x) : { r : ℝ // 0 < r }) : ℝ) =
    ((1 : { r : ℝ // 0 < r }) : ℝ)
  rw [ArakelovDivisor.sizeHom_coe, Positive.val_one, coe_principalDivisor_fst,
    FractionalIdeal.absNorm_span_singleton]
  have hprod := InfinitePlace.prod_eq_abs_norm (K := K) (x : K)
  simp only [coe_principalDivisor_snd] at hprod ⊢
  rw [← hprod]
  apply div_self
  apply ne_of_gt
  apply Finset.prod_pos
  intro w _
  apply pow_pos
  exact InfinitePlace.pos_iff.mpr (Units.ne_zero x)

end NumberField

namespace NumberField

/--
[principalSubgroup_le_degreeZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
lemma principalSubgroup_le_degreeZero
  [Field K] [NumberField K] :
-- imply
  principalSubgroup K ≤ degreeZero K := by
-- proof
  rw [principalSubgroup, degreeZero, MonoidHom.range_le_ker_iff]
  exact MonoidHom.ext fun x => size_principal K x

end NumberField

/--
[absNorm_units_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma absNorm_units_ne_zero_eq
  [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] [Field F] [Algebra R F] [IsFractionRing R F]
  {I : (FractionalIdeal R⁰ F)ˣ} :
-- imply
  absNorm (I : FractionalIdeal R⁰ F) ≠ 0 := by
-- proof
  apply FractionalIdeal.absNorm_units_ne_zero I

/--
[absNorm_units_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma absNorm_units_pos_eq
  [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] [Field F] [Algebra R F] [IsFractionRing R F]
  {I : (FractionalIdeal R⁰ F)ˣ} :
-- imply
  0 < absNorm (I : FractionalIdeal R⁰ F) := by
-- proof
  apply FractionalIdeal.absNorm_units_pos I

/--
[ArakelovDivisor.archimedeanFactor_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma ArakelovDivisor_archimedeanFactor_coe_eq
  [Field K] [NumberField K]
  {D : ArakelovDivisor K} :
-- imply
  (D.archimedeanFactor : ℝ) = ∏ w : InfinitePlace K, (D.2 w : ℝ) ^ w.mult := by
-- proof
  apply NumberField.ArakelovDivisor.archimedeanFactor_coe K D

/--
[ArakelovDivisor.idealNorm_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma ArakelovDivisor_idealNorm_coe_eq
  [Field K] [NumberField K]
  {D : ArakelovDivisor K} :
-- imply
  (D.idealNorm : ℝ) =
    ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) := by
-- proof
  apply NumberField.ArakelovDivisor.idealNorm_coe K D


-- created on 2026-10-20
-- updated on 2026-10-23
