import Mathlib
import Lemma.Definitions.Def_TateCurve_PointSeries

set_option autoImplicit false

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem isometry_of_forall_nnnorm {σ : K →+* K} (h : ∀ x, ‖σ x‖₊ = ‖x‖₊) : Isometry ⇑σ :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← coe_nnnorm, ← coe_nnnorm, h]

theorem map_tsum_of_summable {ι : Type*} (σ : K →+* K) (hσ : Isometry ⇑σ) {f : ι → K}
    (hf : Summable f) : σ (∑' i, f i) = ∑' i, σ (f i) := by
  have h := hf.hasSum.map σ hσ.continuous
  simpa [Function.comp] using h.tsum_eq.symm

theorem map_xfun (σ : K →+* K) (w : K) : σ (xfun w) = xfun (σ w) := by
  simp only [xfun, map_div₀, map_pow, map_sub, map_one]

theorem map_yfun (σ : K →+* K) (w : K) : σ (yfun w) = yfun (σ w) := by
  simp only [yfun, map_div₀, map_pow, map_sub, map_one]

theorem map_term (σ : K →+* K) {q : K} (hσq : σ q = q) (c : ℕ → ℕ) (n : ℕ) :
    σ (term c q n) = term c q n := by
  simp only [term, map_mul, map_natCast, map_div₀, map_pow, map_sub, map_one, hσq]

theorem map_xTerm (σ : K →+* K) {q : K} (hσq : σ q = q) (u : K) (n : ℤ) :
    σ (xTerm q u n) = xTerm q (σ u) n := by
  simp only [xTerm, map_xfun, map_mul, map_zpow₀, hσq]

theorem map_yTerm (σ : K →+* K) {q : K} (hσq : σ q = q) (u : K) (n : ℤ) :
    σ (yTerm q u n) = yTerm q (σ u) n := by
  simp only [yTerm, map_yfun, map_mul, map_zpow₀, hσq]

theorem map_coeffSum (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (c : ℕ → ℕ)
    (hsum : Summable (term c q)) : σ (coeffSum c q) = coeffSum c q := by
  have h := map_tsum_of_summable σ hσ hsum
  simp only [coeffSum]
  rw [h]
  exact tsum_congr fun n => map_term σ hσq c n

variable [CompleteSpace K]

theorem map_s₁ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (s₁ q) = s₁ q := by
  simp only [s₁]
  exact map_coeffSum σ hσ hσq _ (summable_term _ hq)

theorem map_a₄ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (a₄ q) = a₄ q := by
  simp only [a₄, map_neg]
  exact congrArg Neg.neg (map_coeffSum σ hσ hσq _ (summable_term _ hq))

theorem map_a₆ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (a₆ q) = a₆ q := by
  simp only [a₆, map_neg]
  exact congrArg Neg.neg (map_coeffSum σ hσ hσq _ (summable_term _ hq))

theorem map_curve (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    (curve q).map σ = curve q := by
  ext <;>
    simp [curve, WeierstrassCurve.map, map_a₄ σ hσ hσq hq, map_a₆ σ hσ hσq hq]

theorem map_pointX (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointX q u) = pointX q (σ u) := by
  simp only [pointX, map_sub, map_mul, map_ofNat]
  rw [map_s₁ σ hσ hσq hq, map_tsum_of_summable σ hσ (summable_xTerm hq0 hq hu0)]
  congr 1
  exact tsum_congr fun n => map_xTerm σ hσq u n

theorem map_pointY (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointY q u) = pointY q (σ u) := by
  simp only [pointY, map_add]
  rw [map_s₁ σ hσ hσq hq, map_tsum_of_summable σ hσ (summable_yTerm hq0 hq hu0)]
  congr 1
  exact tsum_congr fun n => map_yTerm σ hσq u n

theorem map_pointX_eq_self (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hσu : σ u = u) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointX q u) = pointX q u := by
  rw [map_pointX σ hσ hσq hq0 hq hu0, hσu]

theorem map_pointY_eq_self (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hσu : σ u = u) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointY q u) = pointY q u := by
  rw [map_pointY σ hσ hσq hq0 hq hu0, hσu]

end TateCurve
