import Mathlib
import sympy.Basic
import sympy.series.formal.XnEquivalence
open PowerSeries
open scoped PowerSeries BigOperators Polynomial


/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_refl_is
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (f : R⟦X⟧) :
-- imply
  XnEquiv n f f := by
-- proof
  apply PowerSeries.XnEquiv.refl n f

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_symm_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {f g : R⟦X⟧}
  (h : XnEquiv n f g) :
-- imply
  XnEquiv n g f := by
-- proof
  apply PowerSeries.XnEquiv.symm h

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_trans_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {f g h : R⟦X⟧}
  (hfg : XnEquiv n f g) (hgh : XnEquiv n g h) :
-- imply
  XnEquiv n f h := by
-- proof
  apply PowerSeries.XnEquiv.trans hfg hgh

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_equivalence_is
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) :
-- imply
  Equivalence (XnEquiv n : R⟦X⟧ → R⟦X⟧ → Prop) := by
-- proof
  apply PowerSeries.XnEquiv.equivalence n

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_of_le_is
-- given
  {R : Type*} [CommSemiring R] {m n : ℕ} (hmn : m ≤ n) {f g : R⟦X⟧}
  (h : XnEquiv n f g) :
-- imply
  XnEquiv m f g := by
-- proof
  apply PowerSeries.XnEquiv.of_le hmn h

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_zero_iff
-- given
  {R : Type*} [CommSemiring R] (f g : R⟦X⟧) :
-- imply
  XnEquiv 0 f g ↔ constantCoeff f = constantCoeff g := by
-- proof
  apply PowerSeries.XnEquiv_zero_iff f g

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_self_is
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (f : R⟦X⟧) :
-- imply
  XnEquiv n f f := by
-- proof
  apply PowerSeries.XnEquiv_self n f

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_add_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {a b c d : R⟦X⟧}
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d) :
-- imply
  XnEquiv n (a + c) (b + d) := by
-- proof
  apply PowerSeries.XnEquiv.add hab hcd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_sub_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d) :
-- imply
  XnEquiv n (a - c) (b - d) := by
-- proof
  apply PowerSeries.XnEquiv.sub hab hcd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_smul_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {a b : R⟦X⟧}
  (hab : XnEquiv n a b) (r : R) :
-- imply
  XnEquiv n (r • a) (r • b) := by
-- proof
  apply PowerSeries.XnEquiv.smul hab r

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_mul_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {a b c d : R⟦X⟧}
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d) :
-- imply
  XnEquiv n (a * c) (b * d) := by
-- proof
  apply PowerSeries.XnEquiv.mul hab hcd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_neg_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b : R⟦X⟧}
  (hab : XnEquiv n a b) :
-- imply
  XnEquiv n (-a) (-b) := by
-- proof
  apply PowerSeries.XnEquiv.neg hab

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_inv_of_unit_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b : R⟦X⟧}
  (ua ub : Rˣ) (ha : constantCoeff a = ua) (hb : constantCoeff b = ub)
  (hab : XnEquiv n a b) :
-- imply
  XnEquiv n (invOfUnit a ua) (invOfUnit b ub) := by
-- proof
  apply PowerSeries.XnEquiv.invOfUnit ua ub ha hb hab

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_inv_is
-- given
  {K : Type*} [Field K] {n : ℕ} {a b : K⟦X⟧}
  (ha : constantCoeff a ≠ 0) (hb : constantCoeff b ≠ 0)
  (hab : XnEquiv n a b) :
-- imply
  XnEquiv n a⁻¹ b⁻¹ := by
-- proof
  apply PowerSeries.XnEquiv.inv ha hb hab

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_inv_of_unit'_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} (u v : Rˣ)
  (huv : (u : R) = (v : R))
  (hfg : XnEquiv n f g) :
-- imply
  XnEquiv n (invOfUnit f u) (invOfUnit g v) := by
-- proof
  apply PowerSeries.XnEquiv.invOfUnit' u v huv hfg

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_div_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
  (u v : Rˣ)
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d)
  (hu : constantCoeff c = u) (hv : constantCoeff d = v) :
-- imply
  XnEquiv n (a * invOfUnit c u) (b * invOfUnit d v) := by
-- proof
  apply PowerSeries.XnEquiv.div hab hcd u hu v hv

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_sum_is
-- given
  {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {n : ℕ} {s : Finset ι}
  {a b : ι → R⟦X⟧}
  (h : ∀ i ∈ s, XnEquiv n (a i) (b i)) :
-- imply
  XnEquiv n (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
-- proof
  apply PowerSeries.XnEquiv.sum h

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_prod_is
-- given
  {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {n : ℕ} {s : Finset ι}
  {a b : ι → R⟦X⟧}
  (h : ∀ i ∈ s, XnEquiv n (a i) (b i)) :
-- imply
  XnEquiv n (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
-- proof
  apply PowerSeries.XnEquiv.prod h

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_dvd_iff
-- given
  {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} :
-- imply
  XnEquiv n f g ↔ (X : R⟦X⟧) ^ (n + 1) ∣ f - g := by
-- proof
  apply PowerSeries.xnEquiv_iff_dvd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_sub_eq_mul_x_pow_iff
-- given
  {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} :
-- imply
  XnEquiv n f g ↔ ∃ q : R⟦X⟧, f - g = X ^ (n + 1) * q := by
-- proof
  apply PowerSeries.xnEquiv_iff_sub_eq_mul_X_pow

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_trunc_iff
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {f g : R⟦X⟧} :
-- imply
  XnEquiv n f g ↔ trunc (n + 1) f = trunc (n + 1) g := by
-- proof
  apply PowerSeries.xnEquiv_iff_trunc

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma exists_polynomial_xn_equiv_is
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (f : R⟦X⟧) :
-- imply
  ∃ p : R[X], XnEquiv n f p := by
-- proof
  apply PowerSeries.exists_polynomial_xnEquiv n f

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_pow_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {a b : R⟦X⟧}
  (hab : XnEquiv n a b) (k : ℕ) :
-- imply
  XnEquiv n (a ^ k) (b ^ k) := by
-- proof
  apply PowerSeries.XnEquiv.pow hab k

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_comp_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d)
  (hc : constantCoeff c = 0) (hd : constantCoeff d = 0) :
-- imply
  XnEquiv n (a.subst c) (b.subst d) := by
-- proof
  apply PowerSeries.XnEquiv.comp hab hcd hc hd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma eq_iff_forall_xn_equiv_iff
-- given
  {R : Type*} [CommSemiring R] {f g : R⟦X⟧} :
-- imply
  f = g ↔ ∀ n, XnEquiv n f g := by
-- proof
  apply PowerSeries.eq_iff_forall_xnEquiv


-- created on 2026-10-11
