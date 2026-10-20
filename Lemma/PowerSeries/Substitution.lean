import Mathlib
import sympy.Basic
import sympy.series.formal.Substitution
open PowerSeries
open scoped BigOperators
open AlgebraicCombinatorics
open AlgebraicCombinatorics.FPS (SummableFPS summableFPSSum)


/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_comp_eq_subst
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧) :
-- imply
  fps_comp f g hg = PowerSeries.subst g f := by
-- proof
  apply AlgebraicCombinatorics.fps_comp_eq_subst f g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_comp_coeff
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧)
  (n : ℕ) :
-- imply
  coeff n (PowerSeries.subst g f) = finsum (fun d => coeff d f * coeff n (g ^ d)) := by
-- proof
  apply AlgebraicCombinatorics.fps_comp_coeff f g hg n

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_wd_firstCoeffs
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (n k : ℕ)
  (hg : constantCoeff g = 0)
  (hk : k < n) :
-- imply
  coeff k (g ^ n) = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_wd_firstCoeffs g hg n k hk

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_comp_coeff_finite
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧)
  (n : ℕ) :
-- imply
  coeff n (PowerSeries.subst g f) =
    ∑ d ∈ Finset.range (n + 1), coeff d f * coeff n (g ^ d) := by
-- proof
  apply AlgebraicCombinatorics.fps_comp_coeff_finite f g hg n

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_wd_summable
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧) :
-- imply
  HasSubst g := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_wd_summable f g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_wd_constCoeff
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧) :
-- imply
  constantCoeff (PowerSeries.subst g f) = constantCoeff f := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_wd_constCoeff f g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_fg_coeffs_zero
  [CommRing K]
-- given
  (f g : K⟦X⟧)
  (k : ℕ)
  (hg : constantCoeff g = 0)
  (hf : ∀ m < k, coeff m f = 0) :
-- imply
  ∀ m < k, coeff m (PowerSeries.subst g f) = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_fg_coeffs_zero f g hg k hf

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_add
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f₁ f₂ : K⟦X⟧) :
-- imply
  PowerSeries.subst g (f₁ + f₂) = PowerSeries.subst g f₁ + PowerSeries.subst g f₂ := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_add f₁ f₂ g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_mul
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f₁ f₂ : K⟦X⟧) :
-- imply
  PowerSeries.subst g (f₁ * f₂) = PowerSeries.subst g f₁ * PowerSeries.subst g f₂ := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_mul f₁ f₂ g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_div
  [Field K]
-- given
  (f₂ g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hf₂ : constantCoeff f₂ ≠ 0)
  (f₁ : K⟦X⟧) :
-- imply
  PowerSeries.subst g f₁ * (PowerSeries.subst g f₂)⁻¹ =
    PowerSeries.subst g (f₁ * f₂⁻¹) := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_div f₁ f₂ g hg hf₂

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_pow
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧)
  (k : ℕ) :
-- imply
  PowerSeries.subst g (f ^ k) = (PowerSeries.subst g f) ^ k := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_pow f g hg k

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_assoc_constCoeff
  [CommRing K]
-- given
  (g h : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hh : constantCoeff h = 0) :
-- imply
  constantCoeff (PowerSeries.subst h g) = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_assoc_constCoeff g h hg hh

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_assoc
  [CommRing K]
-- given
  (g h : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hh : constantCoeff h = 0)
  (f : K⟦X⟧) :
-- imply
  PowerSeries.subst h (PowerSeries.subst g f) =
    PowerSeries.subst (PowerSeries.subst h g) f := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_assoc f g h hg hh

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_const
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (a : K) :
-- imply
  PowerSeries.subst g (C a) = C a := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_const a g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_X_left
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0) :
-- imply
  PowerSeries.subst g (X : K⟦X⟧) = g := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_X_left g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_X_right
  [CommRing K]
-- given
  (g : K⟦X⟧) :
-- imply
  PowerSeries.subst X g = g := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_X_right

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_sum
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (s : Finset ι)
  (f : ι → K⟦X⟧) :
-- imply
  PowerSeries.subst g (∑ i ∈ s, f i) = ∑ i ∈ s, PowerSeries.subst g (f i) := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_sum s f g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_summable
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (f : ι → K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hf : SummableFPS f) :
-- imply
  SummableFPS (fun i => PowerSeries.subst g (f i)) := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_summable f g hg hf

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_subs_summableFPSSum
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (f : ι → K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hf : SummableFPS f) :
-- imply
  PowerSeries.subst g (summableFPSSum f hf) =
    summableFPSSum (fun i => PowerSeries.subst g (f i))
      (AlgebraicCombinatorics.fps_subs_summable f g hg hf) := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_summableFPSSum f g hg hf

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma fps_geometric_subst_fibonacci
  [Field K] :
-- imply
  PowerSeries.subst (X + X ^ 2) (geometricSeries (K := K)) = ((1 : K⟦X⟧) - X - X ^ 2)⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fps_geometric_subst_fibonacci

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_self
  [CommRing K] [DecidableEq α]
-- given
  (i : α) :
-- imply
  kroneckerDelta (K := K) i i = 1 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_self

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_ne
  [CommRing K] [DecidableEq α]
-- given
  {i j : α}
  (h : i ≠ j) :
-- imply
  kroneckerDelta (K := K) i j = 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_ne h

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_comm
  [CommRing K] [DecidableEq α]
-- given
  (i j : α) :
-- imply
  kroneckerDelta (K := K) i j = kroneckerDelta j i := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_comm

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_mul_left
  [CommRing K] [DecidableEq α]
-- given
  (i j : α)
  (a : K) :
-- imply
  kroneckerDelta (K := K) i j * a = if i = j then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_mul_left

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_mul_right
  [CommRing K] [DecidableEq α]
-- given
  (i j : α)
  (a : K) :
-- imply
  a * kroneckerDelta (K := K) i j = if i = j then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_mul_right

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma sum_kroneckerDelta_left
  [CommRing K] [DecidableEq α] [Fintype α]
-- given
  (j : α) :
-- imply
  ∑ i, kroneckerDelta (K := K) i j = 1 := by
-- proof
  apply AlgebraicCombinatorics.sum_kroneckerDelta_left

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma sum_kroneckerDelta_right
  [CommRing K] [DecidableEq α] [Fintype α]
-- given
  (i : α) :
-- imply
  ∑ j, kroneckerDelta (K := K) i j = 1 := by
-- proof
  apply AlgebraicCombinatorics.sum_kroneckerDelta_right

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma sum_kroneckerDelta_mul
  [CommRing K] [DecidableEq α] [Fintype α]
-- given
  (j : α)
  (f : α → K) :
-- imply
  ∑ i, kroneckerDelta (K := K) i j * f i = f j := by
-- proof
  apply AlgebraicCombinatorics.sum_kroneckerDelta_mul

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma sum_mul_kroneckerDelta
  [CommRing K] [DecidableEq α] [Fintype α]
-- given
  (i : α)
  (f : α → K) :
-- imply
  ∑ j, f j * kroneckerDelta (K := K) i j = f i := by
-- proof
  apply AlgebraicCombinatorics.sum_mul_kroneckerDelta

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_nat_eq
  [CommRing K]
-- given
  (n m : ℕ) :
-- imply
  kroneckerDelta (K := K) n m = if n = m then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_nat_eq

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_int_eq
  [CommRing K]
-- given
  (n m : ℤ) :
-- imply
  kroneckerDelta (K := K) n m = if n = m then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_int_eq

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_eq_zero_iff
  [CommRing K] [DecidableEq α] [Nontrivial K]
-- given
  {i j : α} :
-- imply
  kroneckerDelta (K := K) i j = 0 ↔ i ≠ j := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_eq_zero_iff

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma kroneckerDelta_eq_one_iff
  [CommRing K] [DecidableEq α] [Nontrivial K]
-- given
  {i j : α} :
-- imply
  kroneckerDelta (K := K) i j = 1 ↔ i = j := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_eq_one_iff


-- created on 2026-10-20
