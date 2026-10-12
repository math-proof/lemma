import Mathlib
import sympy.Basic
import sympy.series.formal.FPSDefinition


/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_mk_eq_symm_eq
  [CommRing R]
-- given
  (a : ℕ → R) :
-- imply
  PowerSeries.mk a = AlgebraicCombinatorics.FPS.fpsEquivSeq.symm a := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_mk_eq_symm a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_coeff_mk_eq
  [CommRing R]
-- given
  (a : ℕ → R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.mk a) = a n := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_coeff_mk a n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_eq_mk_coeff_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  f = PowerSeries.mk (fun n => PowerSeries.coeff n f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_eq_mk_coeff f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_ext_iff
  [CommRing R]
-- given
  (f g : PowerSeries R) :
-- imply
  f = g ↔ ∀ n, PowerSeries.coeff n f = PowerSeries.coeff n g := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_ext_iff f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma zero_fps_eq
  [CommRing R] :
-- imply
  (0 : PowerSeries R) = PowerSeries.mk (fun _ => 0) := by
-- proof
  apply AlgebraicCombinatorics.FPS.zero_fps_eq

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma one_fps_eq
  [CommRing R] :
-- imply
  (1 : PowerSeries R) = PowerSeries.mk (fun n => if n = 0 then 1 else 0) := by
-- proof
  apply AlgebraicCombinatorics.FPS.one_fps_eq

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_add_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff n (f + g) = PowerSeries.coeff n f + PowerSeries.coeff n g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_add_fps n f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_sub_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff n (f - g) = PowerSeries.coeff n f - PowerSeries.coeff n g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_sub_fps n f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_neg_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f : PowerSeries R) :
-- imply
  PowerSeries.coeff n (-f) = -PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_neg_fps n f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_smul_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (c : R)
  (f : PowerSeries R) :
-- imply
  PowerSeries.coeff n (c • f) = c * PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_smul_fps n c f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_mul_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff n (f * g) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_mul_fps n f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_mul_fps'_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff n (f * g) = ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_mul_fps' n f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_C_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (a : R) :
-- imply
  PowerSeries.coeff n (PowerSeries.C a : PowerSeries R) = if n = 0 then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_C_fps n a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_zero_mul_fps_eq
  [CommRing R]
-- given
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_zero_mul_fps f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma smul_mul_fps_eq
  [CommRing R]
-- given
  (c : R)
  (f g : PowerSeries R) :
-- imply
  c • (f * g) = (c • f) * g := by
-- proof
  apply AlgebraicCombinatorics.FPS.smul_mul_fps c f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma smul_mul_fps'_eq
  [CommRing R]
-- given
  (c : R)
  (f g : PowerSeries R) :
-- imply
  c • (f * g) = f * (c • g) := by
-- proof
  apply AlgebraicCombinatorics.FPS.smul_mul_fps' c f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma smul_eq_C_mul_fps_eq
  [CommRing R]
-- given
  (c : R)
  (f : PowerSeries R) :
-- imply
  c • f = PowerSeries.C c * f := by
-- proof
  apply AlgebraicCombinatorics.FPS.smul_eq_C_mul_fps c f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_coeff_one_eq
  [CommRing R] :
-- imply
  PowerSeries.coeff 1 (PowerSeries.X : PowerSeries R) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_coeff_one

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_coeff_ne_one_eq
  [CommRing R]
-- given
  (i : ℕ)
  (hi : i ≠ 1) :
-- imply
  PowerSeries.coeff i (PowerSeries.X : PowerSeries R) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_coeff_ne_one i hi

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_mul_shift_eq
  [CommRing R]
-- given
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_mul_shift f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma mul_X_shift_eq
  [CommRing R]
-- given
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff (n + 1) (f * PowerSeries.X) = PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_X_shift f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_mul_coeff_zero_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_mul_coeff_zero f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma mul_X_coeff_zero_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  PowerSeries.coeff 0 (f * PowerSeries.X) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_X_coeff_zero f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_X_mul_eq
  [CommRing R]
-- given
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.X * f) = if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_X_mul f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_mul_X_eq
  [CommRing R]
-- given
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (f * PowerSeries.X) = if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_mul_X f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_mul_eq_shift_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  PowerSeries.X * f = PowerSeries.mk (fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_mul_eq_shift f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma mul_X_eq_shift_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  f * PowerSeries.X = PowerSeries.mk (fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_X_eq_shift f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_X_pow_mul_eq
  [CommRing R]
-- given
  (k : ℕ)
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.X ^ k * f) = if n < k then 0 else PowerSeries.coeff (n - k) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_X_pow_mul k f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_mul_X_pow_eq
  [CommRing R]
-- given
  (k : ℕ)
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (f * PowerSeries.X ^ k) = if n < k then 0 else PowerSeries.coeff (n - k) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_mul_X_pow k f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_pow_coeff_eq
  [CommRing R]
-- given
  (k n : ℕ) :
-- imply
  PowerSeries.coeff n ((PowerSeries.X : PowerSeries R) ^ k) = if n = k then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_pow_coeff k n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_pow_coeff_self_eq
  [CommRing R]
-- given
  (k : ℕ) :
-- imply
  PowerSeries.coeff k ((PowerSeries.X : PowerSeries R) ^ k) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_pow_coeff_self k

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_eq_tsum_coeff_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  f = PowerSeries.mk (fun n => PowerSeries.coeff n f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_eq_tsum_coeff f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_monomial_mul_X_pow_eq
  [CommRing R]
-- given
  (a : R)
  (k n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.C a * (PowerSeries.X : PowerSeries R) ^ k) = if n = k then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_monomial_mul_X_pow a k n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_summable_fps_sum_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → PowerSeries R)
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (AlgebraicCombinatorics.FPS.summableFPSSum f hf) = finsum fun i => PowerSeries.coeff n (f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_summableFPSSum f hf n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_finsum_finite_is
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → PowerSeries R)
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (n : ℕ) :
-- imply
  (Function.support (fun i => PowerSeries.coeff n (f i))).Finite := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_finsum_finite f hf n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_subfamily_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (J : Set ι) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i : J => f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_subfamily J hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_of_finite_is
  [CommRing R]
  [Finite ι]
-- given
  (f : ι → PowerSeries R) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS f := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_of_finite f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_zero_is
  [CommRing R]
-- given
  (ι : Type*) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun _ : ι => (0 : PowerSeries R)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_zero

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_single_is
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun _ : Unit => f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_single f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_add_is
  [CommRing R]
-- given
  {ι : Type*}
  {f g : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (hg : AlgebraicCombinatorics.FPS.SummableFPS g) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i => f i + g i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_add hf hg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_neg_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i => -f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_neg hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_sub_is
  [CommRing R]
-- given
  {ι : Type*}
  {f g : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (hg : AlgebraicCombinatorics.FPS.SummableFPS g) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i => f i - g i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_sub hf hg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_smul_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (c : R) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i => c • f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_smul c hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_of_essentially_finite_is
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → PowerSeries R)
  (hf : {i | f i ≠ 0}.Finite) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS f := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_of_essentiallyFinite f hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_monomial_family_is
  [CommRing R]
-- given
  (a : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun n => PowerSeries.C (a n) * (PowerSeries.X : PowerSeries R) ^ n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_monomial_family a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_iff_support_finite_iff
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite f ↔ (Function.support f).Finite := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_iff_support_finite f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_subfamily_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (J : Set ι) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i : J => f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_subfamily J hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_of_finite_is
  [CommRing R]
  [Finite ι]
-- given
  (f : ι → R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite f := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_of_finite f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_fintype_is
  [CommRing R]
  [Fintype ι]
-- given
  (f : ι → R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite f := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_fintype f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_zero_is
  [CommRing R]
-- given
  (ι : Type*) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun _ : ι => (0 : R)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_zero

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_add_is
  [CommRing R]
-- given
  {ι : Type*}
  {f g : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hg : AlgebraicCombinatorics.FPS.EssentiallyFinite g) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => f i + g i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_add hf hg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_neg_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => -f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_neg hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_sub_is
  [CommRing R]
-- given
  {ι : Type*}
  {f g : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hg : AlgebraicCombinatorics.FPS.EssentiallyFinite g) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => f i - g i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_sub hf hg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_smul_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (c : R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => c * f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_smul c hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_finset_sum_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = ∑ i ∈ AlgebraicCombinatorics.FPS.essFinSupport hf, f i := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_finset_sum f hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_sum_of_support_subset_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (S : Finset ι)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hS : AlgebraicCombinatorics.FPS.essFinSupport hf ⊆ S) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = ∑ i ∈ S, f i := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_sum_of_support_subset f hf S hS

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_zero_eq
  [CommRing R]
-- given
  {ι : Type*}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite (fun _ : ι => (0 : R))) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum (fun _ => 0) hf = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_zero hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_zero_of_forall_zero_eq
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (h : ∀ i, f i = 0) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_zero_of_forall_zero hf h

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_sum_finset_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (S : Finset ι)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hS : ∀ i, f i ≠ 0 → i ∈ S) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = ∑ i ∈ S, f i := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_sum_finset f hf S hS

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_single_is
  [CommRing R]
  [DecidableEq ι]
-- given
  (i : ι)
  (a : R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun j => if j = i then a else 0) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_single i a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_to_finsupp_apply_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (i : ι) :
-- imply
  AlgebraicCombinatorics.FPS.essentiallyFiniteToFinsupp f hf i = f i := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFiniteToFinsupp_apply f hf i

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_finsupp_sum_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = (AlgebraicCombinatorics.FPS.essentiallyFiniteToFinsupp f hf).sum (fun _ r => r) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_finsupp_sum f hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_add_eq
  [CommRing R]
  [DecidableEq ι]
-- given
  {f g : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hg : AlgebraicCombinatorics.FPS.EssentiallyFinite g)
  (hfg : AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => f i + g i)) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum (fun i => f i + g i) hfg = AlgebraicCombinatorics.FPS.essFinSum f hf + AlgebraicCombinatorics.FPS.essFinSum g hg := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_add hf hg hfg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_smul_eq
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (c : R)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hcf : AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => c * f i)) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum (fun i => c * f i) hcf = c * AlgebraicCombinatorics.FPS.essFinSum f hf := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_smul c hf hcf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_fubini_is
  [CommRing R]
-- given
  {ι κ : Type*}
  {f : ι × κ → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f) :
-- imply
  (∀ i, AlgebraicCombinatorics.FPS.SummableFPS (fun j => f (i, j))) ∧ (∀ j, AlgebraicCombinatorics.FPS.SummableFPS (fun i => f (i, j))) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_fubini hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_coeff_eq
  [CommRing R]
-- given
  (a : ℕ → R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (AlgebraicCombinatorics.FPS.generatingFunction a) = a n := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_coeff a n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_zero_eq
  [CommRing R] :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (0 : ℕ → R) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_zero

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_add_eq
  [CommRing R]
-- given
  (a b : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (a + b) = AlgebraicCombinatorics.FPS.generatingFunction a + AlgebraicCombinatorics.FPS.generatingFunction b := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_add a b

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_neg_eq
  [CommRing R]
-- given
  (a : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (-a) = -AlgebraicCombinatorics.FPS.generatingFunction a := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_neg a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_smul_eq
  [CommRing R]
-- given
  (c : R)
  (a : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (c • a) = c • AlgebraicCombinatorics.FPS.generatingFunction a := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_smul c a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_sub_eq
  [CommRing R]
-- given
  (a b : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (a - b) = AlgebraicCombinatorics.FPS.generatingFunction a - AlgebraicCombinatorics.FPS.generatingFunction b := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_sub a b

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_one_eq
  [CommRing R] :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (fun n => if n = 0 then (1 : R) else 0) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_one

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma vandermonde_nat_eq
-- given
  (a b n : ℕ) :
-- imply
  (a + b).choose n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a.choose ij.1 * b.choose ij.2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.vandermonde_nat a b n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma vandermonde_nat'_eq
-- given
  (a b n : ℕ) :
-- imply
  (a + b).choose n = ∑ k ∈ Finset.range (n + 1), a.choose k * b.choose (n - k) := by
-- proof
  apply AlgebraicCombinatorics.FPS.vandermonde_nat' a b n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma chu_vandermonde_eq
  [CommRing S]
  [BinomialRing S]
-- given
  (a b : S)
  (n : ℕ) :
-- imply
  Ring.choose (a + b) n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, Ring.choose a ij.1 * Ring.choose b ij.2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.chuVandermonde a b n


-- created on 2026-10-12
