import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.ArakelovDivisor
open scoped NumberField nonZeroDivisors
open FractionalIdeal
open NumberField


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

/--
[ArakelovDivisor.sizeHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma ArakelovDivisor_sizeHom_apply_eq
  [Field K] [NumberField K]
  {D : ArakelovDivisor K} :
-- imply
  ArakelovDivisor.sizeHom K D =
    ArakelovDivisor.archHom K D / ArakelovDivisor.idealHom K D := by
-- proof
  apply NumberField.ArakelovDivisor.sizeHom_apply K D

/--
[ArakelovDivisor.sizeHom_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma ArakelovDivisor_sizeHom_coe_eq
  [Field K] [NumberField K]
  {D : ArakelovDivisor K} :
-- imply
  (ArakelovDivisor.sizeHom K D : ℝ) =
    (∏ w : InfinitePlace K, (D.2 w : ℝ) ^ w.mult) /
    ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) := by
-- proof
  apply NumberField.ArakelovDivisor.sizeHom_coe K D

/--
[ArakelovDivisor.mem_sectionSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma ArakelovDivisor_mem_sectionSet_eq
  [Field K] [NumberField K]
  {D : ArakelovDivisor K}
  {x : K} :
-- imply
  x ∈ D.sectionSet ↔
    x ∈ (D.1 : FractionalIdeal (𝓞 K)⁰ K) ∧
    ∀ w : InfinitePlace K, w x ≤ (D.2 w : ℝ) := by
-- proof
  apply NumberField.ArakelovDivisor.mem_sectionSet K D x

/--
[ArakelovDivisor.sectionSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma ArakelovDivisor_sectionSet_finite_eq
  [Field K] [NumberField K]
  {D : ArakelovDivisor K} :
-- imply
  D.sectionSet.Finite := by
-- proof
  apply NumberField.ArakelovDivisor.sectionSet_finite K D

/--
[coe_principalDivisor_snd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma coe_principalDivisor_snd_eq
  [Field K] [NumberField K]
  {x : Kˣ}
  {w : InfinitePlace K} :
-- imply
  (((principalDivisor K x).2 w : { r : ℝ // 0 < r }) : ℝ) = w (x : K) := by
-- proof
  apply NumberField.coe_principalDivisor_snd K x w

/--
[coe_principalDivisor_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma coe_principalDivisor_fst_eq
  [Field K] [NumberField K]
  {x : Kˣ} :
-- imply
  ((principalDivisor K x).1 : FractionalIdeal (𝓞 K)⁰ K) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) := by
-- proof
  apply NumberField.coe_principalDivisor_fst K x

/--
[size_principal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma size_principal_eq
  [Field K] [NumberField K]
  {x : Kˣ} :
-- imply
  ArakelovDivisor.sizeHom K (principalHom K x) = 1 := by
-- proof
  apply NumberField.size_principal K x

/--
[principalSubgroup_le_degreeZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ArakelovDivisor.lean)
-/
@[path]
private lemma principalSubgroup_le_degreeZero_eq
  [Field K] [NumberField K] :
-- imply
  principalSubgroup K ≤ degreeZero K := by
-- proof
  apply NumberField.principalSubgroup_le_degreeZero K


-- created on 2026-10-20
