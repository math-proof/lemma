import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[cubic_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma cubic_monic (W : WeierstrassCurve F) : (cubic W).Monic := by
  unfold cubic
  monicity <;> norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[cubic_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma cubic_natDegree (W : WeierstrassCurve F) : (cubic W).natDegree = 3 := by
  unfold cubic
  compute_degree <;> norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[duplicationNumerator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma duplicationNumerator_eq (W : WeierstrassCurve F) :
  duplicationNumerator W =
    (cubic W).derivative ^ 2 -
      C 4 * (C W.a₂ + C 2 * X) * cubic W := by
  simp only [duplicationNumerator, cubic, derivative_add, derivative_pow,
    derivative_X, derivative_C, derivative_mul, map_ofNat]
  simp only [C_eq_natCast, C_ofNat, map_mul, map_sub, map_pow]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma product_formula {R : Type*} [CommRing R]
  (a b c t f g : R) :
  let cubicAtT := t ^ 3 + a * t ^ 2 + b * t + c
  let common :=
    (t * g + f) * (b * g + t * f) + 2 * g * (a * t * f + c * g)
  common ^ 2 -
    4 * cubicAtT * g * (f ^ 3 + a * f ^ 2 * g + b * f * g ^ 2 + c * g ^ 3) =
    (t * g - f) ^ 2 *
      ((t * f - b * g) ^ 2 - 4 * c * g * ((t + a) * g + f)) := by
  dsimp only
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_cubicRat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_cubicRat (W : WeierstrassCurve F) :
  (cubicRat W).intDegree = 3 := by
  rw [cubicRat, RatFunc.intDegree_polynomial, cubic_natDegree]
  norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_pow {x : RatFunc F} (hx : x ≠ 0) (n : ℕ) :
  (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_add_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_add_le_of_le {x y : RatFunc F} {m : ℤ}
  (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m) :
  (x + y).intDegree ≤ m := by
  by_cases hxy : x + y = 0
  · simp [hxy, hm]
  by_cases hy0 : y = 0
  · simpa [hy0] using hx
  exact (RatFunc.intDegree_add_le hy0 hxy).trans (max_le hx hy)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_add_sub_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_add_sub_le_of_le {x y z : RatFunc F} {m : ℤ}
  (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m)
  (hz : z.intDegree ≤ m) : (x + y - z).intDegree ≤ m := by
  rw [sub_eq_add_neg]
  apply intDegree_add_le_of_le (x := x + y) (y := -z) hm
  · exact intDegree_add_le_of_le (x := x) (y := y) hm hx hy
  · rw [RatFunc.intDegree_neg]
    exact hz

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_mul_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_mul_le_of_le {x y : RatFunc F} {m n : ℤ}
  (hmn : 0 ≤ m + n) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ n) :
  (x * y).intDegree ≤ m + n := by
  by_cases hx0 : x = 0
  · simp [hx0, hmn]
  by_cases hy0 : y = 0
  · simp [hy0, hmn]
  rw [RatFunc.intDegree_mul hx0 hy0]
  exact add_le_add hx hy

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_pow_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_pow_le_zero {x : RatFunc F} (hx : x.intDegree ≤ 0) (n : ℕ) :
  (x ^ n).intDegree ≤ 0 := by
  by_cases hx0 : x = 0
  · cases n <;> simp [hx0]
  rw [intDegree_pow hx0]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hx

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_cubic_paperX_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_cubic_paperX_le_zero (W : WeierstrassCurve F)
  {x : RatFunc F} (hx : x.intDegree ≤ 0) :
  (x ^ 3 + RatFunc.C W.a₂ * x ^ 2 + RatFunc.C W.a₄ * x +
    RatFunc.C W.a₆).intDegree ≤ 0 := by
  have hx3 : (x ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
  have hx2 : (x ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hx 2
  have ha2 : (RatFunc.C W.a₂ * x ^ 2).intDegree ≤ 0 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₂) (y := x ^ 2)
      (m := 0) (n := 0) (by norm_num) (by simp) hx2
  have ha4 : (RatFunc.C W.a₄ * x).intDegree ≤ 0 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₄) (y := x)
      (m := 0) (n := 0) (by norm_num) (by simp) hx
  have h₁ := intDegree_add_le_of_le (m := 0) (by norm_num) hx3 ha2
  have h₂ := intDegree_add_le_of_le (m := 0) (by norm_num) h₁ ha4
  exact intDegree_add_le_of_le (m := 0) (by norm_num) h₂ (by simp)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_canceled_numerator_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_canceled_numerator_le_two
  (A r s : RatFunc F) (a b c : F) (hr : r.intDegree ≤ 0)
  (hAs : (A * s).intDegree ≤ 1) :
  ((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
    2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) -
    2 * A * s).intDegree ≤ 2 := by
  have hXr : (RatFunc.X * r).intDegree ≤ 1 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.X) (y := r)
      (m := 1) (n := 0) (by norm_num) (by simp) hr
  have hXadd : (RatFunc.X + r).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) (by simp) (hr.trans (by norm_num))
  have hbXr : (RatFunc.C b + RatFunc.X * r).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) (by simp) hXr
  have hfirst :
    ((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r)).intDegree ≤ 2 := by
    simpa using intDegree_mul_le_of_le
      (x := RatFunc.X + r) (y := RatFunc.C b + RatFunc.X * r)
      (m := 1) (n := 1) (by norm_num) hXadd hbXr
  have haXr : (RatFunc.C a * RatFunc.X * r).intDegree ≤ 1 := by
    have haX : (RatFunc.C a * RatFunc.X).intDegree ≤ 1 := by
      simpa using intDegree_mul_le_of_le (x := RatFunc.C a) (y := RatFunc.X)
        (m := 0) (n := 1) (by norm_num) (by simp) (by simp)
    simpa [mul_assoc] using intDegree_mul_le_of_le
      (x := RatFunc.C a * RatFunc.X) (y := r)
      (m := 1) (n := 0) (by norm_num) haX hr
  have hmiddleInside :
    (RatFunc.C a * RatFunc.X * r + RatFunc.C c).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) haXr (by simp)
  have hmiddle :
    (2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c)).intDegree ≤ 1 := by
    rw [show 2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) =
      (RatFunc.C a * RatFunc.X * r + RatFunc.C c) +
        (RatFunc.C a * RatFunc.X * r + RatFunc.C c) by ring]
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hmiddleInside hmiddleInside
  have hlast : (2 * A * s).intDegree ≤ 1 := by
    rw [show 2 * A * s = A * s + A * s by ring]
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hAs hAs
  exact intDegree_add_sub_le_of_le
    (x := (RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r))
    (y := 2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c))
    (z := 2 * A * s) (m := 2) (by norm_num) hfirst
      (hmiddle.trans (by norm_num)) (hlast.trans (by norm_num))

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_X_sub_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_X_sub_eq_one {r : RatFunc F} (hr : r.intDegree ≤ 0) :
  (RatFunc.X - r).intDegree = 1 := by
  have hneg : (-r).intDegree ≤ 1 := by
    rw [RatFunc.intDegree_neg]
    exact hr.trans (by norm_num)
  have hdiffLe : (RatFunc.X - r).intDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    exact intDegree_add_le_of_le (x := RatFunc.X) (y := -r)
      (m := 1) (by norm_num) (by simp) hneg
  have hdiffNotLe : ¬(RatFunc.X - r).intDegree ≤ 0 := by
    intro hdiff
    have hbad : (RatFunc.X : RatFunc F).intDegree ≤ 0 := by
      rw [show (RatFunc.X : RatFunc F) = (RatFunc.X - r) + r by ring]
      exact intDegree_add_le_of_le (x := RatFunc.X - r) (y := r)
        (m := 0) (by norm_num) hdiff hr
    norm_num at hbad
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[intDegree_canceled_expression_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma intDegree_canceled_expression_le_zero
  (A r s : RatFunc F) (a b c : F) (hr : r.intDegree ≤ 0)
  (hAs : (A * s).intDegree ≤ 1) :
  (((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
    2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) - 2 * A * s) /
    (RatFunc.X - r) ^ 2).intDegree ≤ 0 := by
  let numerator :=
    (RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
      2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) - 2 * A * s
  have hnumerator : numerator.intDegree ≤ 2 := by
    dsimp only [numerator]
    exact intDegree_canceled_numerator_le_two A r s a b c hr hAs
  have hdiffDegree : (RatFunc.X - r).intDegree = 1 := intDegree_X_sub_eq_one hr
  have hdiffNe : RatFunc.X - r ≠ 0 := by
    intro h
    rw [h] at hdiffDegree
    simp at hdiffDegree
  have hdenDegree : ((RatFunc.X - r) ^ 2).intDegree = 2 := by
    rw [intDegree_pow hdiffNe, hdiffDegree]
    norm_num
  change (numerator / (RatFunc.X - r) ^ 2).intDegree ≤ 0
  by_cases hn0 : numerator = 0
  · simp [hn0]
  rw [RatFunc.intDegree_div hn0 (pow_ne_zero 2 hdiffNe), hdenDegree]
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[badAtInfinity_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma badAtInfinity_neg (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] [W.IsElliptic] (P : (twist W).toAffine.Point) :
  badAtInfinity W (-P) ↔ badAtInfinity W P := by
  cases P with
  | zero => rfl
  | some x y hxy =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    rfl

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[point_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma point_add_one [Finite F] (hchar : ringChar F ≠ 2)
  (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
  point hchar W (n + 1) = point hchar W n + Q W := by
  rw [point, point, add_one_zsmul]
  abel

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[Q_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma Q_ne_zero (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
  Q W ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[cubic_pow_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma cubic_pow_card [Finite F] (W : WeierstrassCurve F) :
  cubic W ^ Nat.card F =
    X ^ (3 * Nat.card F) + C W.a₂ * X ^ (2 * Nat.card F) +
      C W.a₄ * X ^ Nat.card F + C W.a₆ := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  rw [← FiniteField.Polynomial.expand_card]
  simp only [cubic, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[natDegree_add_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma natDegree_add_le_of_le {p q : F[X]} {n : ℕ}
  (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
  (p + q).natDegree ≤ n :=
  (Polynomial.natDegree_add_le p q).trans (max_le hp hq)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[algebraMap_frobeniusPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma algebraMap_frobeniusPolynomial [Finite F] :
  algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) =
    RatFunc.X ^ Nat.card F - RatFunc.X := by
  simp [frobeniusPolynomial, RatFunc.algebraMap_X]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[two_ne_zero_of_ringChar_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma two_ne_zero_of_ringChar_ne_two (hchar : ringChar F ≠ 2) :
  (2 : F) ≠ 0 := by
  let _ : CharP F (ringChar F) := ringChar.charP F
  intro htwo
  have hdvd : ringChar F ∣ 2 :=
    (CharP.cast_eq_zero_iff F (ringChar F) 2).mp htwo
  obtain hone | htwoChar := (Nat.dvd_prime Nat.prime_two).mp hdvd
  · have hcast : ((1 : ℕ) : F) = 0 :=
    (CharP.cast_eq_zero_iff F (ringChar F) 1).mpr (by simp [hone])
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa only [Nat.cast_one] using hcast)
  · exact hchar htwoChar

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[squareFiber_natCard_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma squareFiber_natCard_eq_one [Finite F] (W : WeierstrassCurve F)
  (x : F) (hzero : (cubic W).eval x = 0) :
  Nat.card (squareFiber W x) = 1 := by
  let _ : Nonempty (squareFiber W x) :=
    ⟨⟨0, by simp [hzero]⟩⟩
  let _ : Subsingleton (squareFiber W x) := ⟨by
    intro y z
    apply Subtype.ext
    have hy : y.1 = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using y.2)
    have hz : z.1 = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using z.2)
    rw [hy, hz]⟩
  exact Nat.card_unique

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[squareFiber_natCard_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma squareFiber_natCard_eq_two [Finite F]
  (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
  (hzero : (cubic W).eval x ≠ 0)
  (hsquare : IsSquare ((cubic W).eval x)) :
  Nat.card (squareFiber W x) = 2 := by
  classical
  obtain ⟨r, hr⟩ := hsquare
  have hrpow : r ^ 2 = (cubic W).eval x := by
    simpa [pow_two] using hr.symm
  have hrzero : r ≠ 0 := by
    intro hr0
    apply hzero
    rw [← hrpow, hr0]
    simp
  have hneg : -r ≠ r := by
    intro h
    have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
    have hadd : r + r = 0 := by
      calc
        r + r = -r + r := congrArg (fun z : F ↦ z + r) h.symm
        _ = 0 := neg_add_cancel r
    have hproduct : (2 : F) * r = 0 := by
      rwa [two_mul]
    exact hrzero ((mul_eq_zero.mp hproduct).resolve_left htwo)
  let e : squareFiber W x ≃ Bool :=
    { toFun := fun y ↦ if y.1 = r then true else false
      invFun := fun b ↦ match b with
        | true => ⟨r, hrpow⟩
        | false => ⟨-r, by simpa using hrpow⟩
      left_inv := by
        intro y
        have hy : y.1 = r ∨ y.1 = -r :=
          (sq_eq_sq_iff_eq_or_eq_neg).mp (y.2.trans hrpow.symm)
        apply Subtype.ext
        obtain hy | hy := hy
        · simp [hy]
        · simp [hy, hneg]
      right_inv := by
        intro b
        cases b <;> simp [hneg] }
  simpa using Nat.card_congr e

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[squareFiber_natCard_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma squareFiber_natCard_eq_zero [Finite F]
  (W : WeierstrassCurve F) (x : F)
  (hsquare : ¬IsSquare ((cubic W).eval x)) :
  Nat.card (squareFiber W x) = 0 := by
  let _ : IsEmpty (squareFiber W x) := ⟨fun y ↦ hsquare ⟨y.1, by
    simpa [pow_two] using y.2.symm⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[eval_frobeniusPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma eval_frobeniusPolynomial [Finite F] (x : F) :
  (frobeniusPolynomial : F[X]).eval x = 0 := by
  let _ : Fintype F := Fintype.ofFinite F
  unfold frobeniusPolynomial
  rw [eval_sub, eval_pow, eval_X, Nat.card_eq_fintype_card,
    FiniteField.pow_card, sub_self]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[eval_minusOneNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma eval_minusOneNumerator [Finite F]
  (W : WeierstrassCurve F) (x : F) :
  (minusOneNumerator W).eval x =
    (cubic W).eval x * ((eulerPolynomial W).eval x + 1) ^ 2 := by
  unfold minusOneNumerator
  simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_one]
  rw [eval_frobeniusPolynomial]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[eval_derivative_eq_zero_of_sq_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma eval_derivative_eq_zero_of_sq_dvd {p : F[X]} {x : F}
  (hdiv : (X - C x) ^ 2 ∣ p) : p.derivative.eval x = 0 := by
  obtain ⟨q, rfl⟩ := hdiv
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X,
    derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[count_roots_frobeniusPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma count_roots_frobeniusPolynomial [Finite F] (x : F) :
  Multiset.count x (frobeniusPolynomial : F[X]).roots = 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  unfold frobeniusPolynomial
  rw [Nat.card_eq_fintype_card, FiniteField.roots_X_pow_card_sub_X]
  simp

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[count_roots_frobeniusPolynomial_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma count_roots_frobeniusPolynomial_sq [Finite F] (x : F) :
  Multiset.count x ((frobeniusPolynomial : F[X]) ^ 2).roots = 2 := by
  rw [Polynomial.roots_pow, Multiset.count_nsmul,
    count_roots_frobeniusPolynomial]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[frobeniusPolynomial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma frobeniusPolynomial_ne_zero [Finite F] :
  (frobeniusPolynomial : F[X]) ≠ 0 := by
  intro hzero
  have hcount := count_roots_frobeniusPolynomial (F := F) 0
  rw [hzero] at hcount
  simp at hcount

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[squareFiber_natCard_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma squareFiber_natCard_le_two [Finite F]
  (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F) :
  Nat.card (squareFiber W x) ≤ 2 := by
  by_cases hzero : (cubic W).eval x = 0
  · rw [squareFiber_natCard_eq_one W x hzero]
    omega
  by_cases hsquare : IsSquare ((cubic W).eval x)
  · rw [squareFiber_natCard_eq_two hchar W x hzero hsquare]
  · rw [squareFiber_natCard_eq_zero W x hsquare]
    omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[frobeniusPolynomial_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma frobeniusPolynomial_splits [Finite F] :
  (frobeniusPolynomial : F[X]).Splits := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Polynomial.splits_iff_card_roots]
  unfold frobeniusPolynomial
  rw [Nat.card_eq_fintype_card, FiniteField.roots_X_pow_card_sub_X,
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  simp

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[pointCount_eq_fiber_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma pointCount_eq_fiber_sum [Fintype F]
  (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
  Nat.card W.toAffine.Point =
    (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivSquareFibers W), Nat.card_sigma]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[natDegree_num_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma natDegree_num_div (p q : F[X]) (hq : q ≠ 0) :
  (RatFunc.num
    (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q)).natDegree =
    (p / gcd p q).natDegree := by
  have hg : gcd p q ≠ 0 := by
    intro hzero
    exact hq ((gcd_eq_zero_iff _ _).mp hzero).2
  have hgdivq : gcd p q ∣ q := gcd_dvd_right _ _
  have hmul :
    gcd p q * (q / gcd p q) = q :=
    EuclideanDomain.mul_div_cancel' hg hgdivq
  have hquotient : q / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hq hmul.symm
  rw [RatFunc.num_div, Polynomial.natDegree_C_mul]
  exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hquotient)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[symmetricOutput_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma symmetricOutput_zero (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] (f g : F[X]) :
  symmetricOutput W f g 0 =
    (X * f) ^ 2 - C (2 * W.a₄) * (X * f) * g -
      C (4 * W.a₆) * (X * g + f) * g -
        C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [C_ofNat]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[symmetricOutput_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma symmetricOutput_one (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] (f g : F[X]) :
  symmetricOutput W f g 1 =
    C 2 * (X * g + f) * (X * f) +
      C (4 * W.a₂) * (X * f) * g +
        C (2 * W.a₄) * (X * g + f) * g + C (4 * W.a₆) * g ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [C_ofNat]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[symmetricOutput_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma symmetricOutput_two (W : WeierstrassCurve F)
  (f g : F[X]) :
  symmetricOutput W f g 2 = (X * g - f) ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[primitive_symmetricOutput](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma primitive_symmetricOutput (W : WeierstrassCurve F)
  [W.IsElliptic] {f g : F[X]} (hfg : IsCoprime f g)
  (hh : X * g - f ≠ 0) :
  PrimitiveTriple (symmetricOutput W f g 0)
    (symmetricOutput W f g 1) (symmetricOutput W f g 2) := by
  apply primitiveTriple_of_no_common_irreducible
  · rw [symmetricOutput_two]
    exact pow_ne_zero 2 hh
  · intro p hp hp0 hp1 hp2
    have hout : ∀ i : Fin 3, p ∣ symmetricOutput W f g i := by
      intro i
      fin_cases i
      · exact hp0
      · exact hp1
      · exact hp2
    have hinPow (i : Fin 3) : p ∣ symmetricInput f g i ^ 4 := by
      rw [← (W.map C).addSubMapCoeff_condition (symmetricInput f g) i]
      apply Finset.dvd_sum
      intro j _
      exact (hout j).mul_left _
    have hin (i : Fin 3) : p ∣ symmetricInput f g i :=
      hp.prime.dvd_of_dvd_pow (hinPow i)
    have hpg : p ∣ g := by simpa [symmetricInput] using hin 2
    have hpf : p ∣ f := by
      have hdiff := (hin 1).sub (hpg.mul_left X)
      simpa [symmetricInput] using hdiff
    exact hp.not_isUnit (hfg.isUnit_of_dvd' hpf hpg)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[symmetricOutput_zero_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma symmetricOutput_zero_natDegree (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] {f g : F[X]} (hf : f ≠ 0)
  (hdegree : g.natDegree < f.natDegree) :
  (symmetricOutput W f g 0).natDegree = 2 * f.natDegree + 2 := by
  let t₁ := C (2 * W.a₄) * (X * f) * g
  let t₂ := C (4 * W.a₆) * (X * g + f) * g
  let t₃ := C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2
  let remainder := t₁ + t₂ + t₃
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hXg : (X * g).natDegree ≤ f.natDegree := by
    calc
      (X * g).natDegree ≤ X.natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ f.natDegree := by rw [Polynomial.natDegree_X]; omega
  have hXgAdd : (X * g + f).natDegree ≤ f.natDegree :=
    (Polynomial.natDegree_add_le (X * g) f).trans (max_le hXg le_rfl)
  have ht₁ : t₁.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₁]
    calc
      (C (2 * W.a₄) * (X * f) * g).natDegree ≤
        (C (2 * W.a₄) * (X * f)).natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (X * f).natDegree + g.natDegree :=
        Nat.add_le_add_right
          (Polynomial.natDegree_C_mul_le (2 * W.a₄) (X * f)) g.natDegree
      _ ≤ 2 * f.natDegree := by rw [hXf]; omega
  have ht₂ : t₂.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₂]
    calc
      (C (4 * W.a₆) * (X * g + f) * g).natDegree ≤
        (C (4 * W.a₆) * (X * g + f)).natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (X * g + f).natDegree + g.natDegree :=
        Nat.add_le_add_right
          (Polynomial.natDegree_C_mul_le (4 * W.a₆) (X * g + f)) g.natDegree
      _ ≤ 2 * f.natDegree := by omega
  have ht₃ : t₃.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₃]
    calc
      (C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2).natDegree ≤
        (g ^ 2).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
      _ ≤ 2 * f.natDegree := by omega
  have hremainder : remainder.natDegree ≤ 2 * f.natDegree := by
    dsimp only [remainder]
    exact (Polynomial.natDegree_add_le (t₁ + t₂) t₃).trans
      (max_le
        ((Polynomial.natDegree_add_le t₁ t₂).trans (max_le ht₁ ht₂)) ht₃)
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  rw [symmetricOutput_zero]
  have heq :
    (X * f) ^ 2 - C (2 * W.a₄) * (X * f) * g -
      C (4 * W.a₆) * (X * g + f) * g -
        C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2 =
      (X * f) ^ 2 - remainder := by
    dsimp only [remainder, t₁, t₂, t₃]
    ring
  rw [heq]
  calc
    ((X * f) ^ 2 - remainder).natDegree = ((X * f) ^ 2).natDegree := by
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      rw [hmain]
      omega
    _ = 2 * f.natDegree + 2 := hmain

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[algebraMap_symmetricOutput_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma algebraMap_symmetricOutput_zero (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] (r : RatFunc F) :
  algebraMap F[X] (RatFunc F)
    (symmetricOutput W r.num r.denom 0) =
    algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricFirstRat W r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_zero]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  rw [hr]
  unfold symmetricFirstRat
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[algebraMap_symmetricOutput_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma algebraMap_symmetricOutput_one (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] (r : RatFunc F) :
  algebraMap F[X] (RatFunc F)
    (symmetricOutput W r.num r.denom 1) =
    algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricSecondRat W r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_one]
  simp only [map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  rw [hr]
  unfold symmetricSecondRat additionCommon
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[algebraMap_symmetricOutput_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma algebraMap_symmetricOutput_two (W : WeierstrassCurve F)
  (r : RatFunc F) :
  algebraMap F[X] (RatFunc F)
    (symmetricOutput W r.num r.denom 2) =
    algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricDenominatorRat r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_two]
  simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_X]
  rw [hr]
  unfold symmetricDenominatorRat
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[symmetricOutput_zero_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma symmetricOutput_zero_ratio (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] (r : RatFunc F) :
  algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 0) /
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
    symmetricFirstRat W r / symmetricDenominatorRat r := by
  rw [algebraMap_symmetricOutput_zero, algebraMap_symmetricOutput_two]
  field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[symmetricOutput_one_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma symmetricOutput_one_ratio (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] (r : RatFunc F) :
  algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 1) /
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
    symmetricSecondRat W r / symmetricDenominatorRat r := by
  rw [algebraMap_symmetricOutput_one, algebraMap_symmetricOutput_two]
  field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[symmetricOutput_pair_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma symmetricOutput_pair_sum (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] (r s : RatFunc F) (hdiff : RatFunc.X - r ≠ 0) :
  algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 1) /
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
    (additionCommon W r - 2 * cubicRat W * s) /
      (RatFunc.X - r) ^ 2 +
      (additionCommon W r + 2 * cubicRat W * s) /
        (RatFunc.X - r) ^ 2 := by
  rw [symmetricOutput_one_ratio]
  unfold symmetricSecondRat symmetricDenominatorRat
  field_simp [hdiff]
  unfold additionCommon
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[paperY_negY](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma paperY_negY (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) :
  paperY W ((twist W).toAffine.negY x y) = -paperY W y := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  unfold paperY
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[X_mul_denom_sub_num_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma X_mul_denom_sub_num_ne_zero {r : RatFunc F}
  (h : RatFunc.X - r ≠ 0) : X * r.denom - r.num ≠ 0 := by
  intro hzero
  apply h
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  have hmap := congrArg (algebraMap F[X] (RatFunc F)) hzero
  simp only [map_sub, map_mul, map_zero, RatFunc.algebraMap_X] at hmap
  rw [hnum] at hmap
  apply (mul_eq_zero.mp ?_).resolve_right hden
  linear_combination hmap

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[ratFunc_ne_zero_of_num_degree_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma ratFunc_ne_zero_of_num_degree_gt {r : RatFunc F}
  (hdegree : r.denom.natDegree < r.num.natDegree) : r ≠ 0 := by
  intro hzero
  rw [hzero] at hdegree
  simp at hdegree

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[four_ne_zero_of_ringChar_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma four_ne_zero_of_ringChar_ne_two (hchar : ringChar F ≠ 2) :
  (4 : F) ≠ 0 := by
  have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  intro hfour
  have hmul : (2 : F) * 2 = 0 := by
    calc
      (2 : F) * 2 = 4 := by norm_num
      _ = 0 := hfour
  obtain hzero | hzero := mul_eq_zero.mp hmul
  · exact htwo hzero
  · exact htwo hzero

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[duplicationNumerator_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma duplicationNumerator_natDegree (W : WeierstrassCurve F) :
  (duplicationNumerator W).natDegree = 4 := by
  unfold duplicationNumerator
  compute_degree <;> norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[natDegree_num_div_of_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma natDegree_num_div_of_isCoprime (p q : F[X])
  (hp : p ≠ 0) (hq : q ≠ 0) (hcop : IsCoprime p q) :
  (RatFunc.num
    (algebraMap F[X] (RatFunc F) p /
      algebraMap F[X] (RatFunc F) q)).natDegree = p.natDegree := by
  rw [natDegree_num_div p q hq]
  have hgUnit : IsUnit (gcd p q) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg : gcd p q ≠ 0 := hgUnit.ne_zero
  have hmul : gcd p q * (p / gcd p q) = p :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hquot : p / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hp hmul.symm
  have hdegree := Polynomial.natDegree_mul hg hquot
  rwa [hmul, Polynomial.natDegree_eq_zero_of_isUnit hgUnit, zero_add] at hdegree

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[point_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma point_sub_one [Finite F] (hchar : ringChar F ≠ 2)
  (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
  point hchar W (n - 1) = point hchar W n - Q W := by
  have hstep := point_add_one hchar W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[ringChar_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma ringChar_ne_two (W : WeierstrassCurve F)
  [W.IsCharNeTwoNF] [W.IsElliptic] : ringChar F ≠ 2 := by
  intro hchar
  let _ : CharP F 2 := ringChar.of_eq hchar
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h16 : (16 : F) = 0 := by
    calc
      (16 : F) = (2 : F) * 8 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h64 : (64 : F) = 0 := by
    calc
      (64 : F) = (2 : F) * 32 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h288 : (288 : F) = 0 := by
    calc
      (288 : F) = (2 : F) * 144 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h432 : (432 : F) = 0 := by
    calc
      (432 : F) = (2 : F) * 216 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have hdelta : W.Δ = 0 := by
    rw [WeierstrassCurve.Δ_of_isCharNeTwoNF, h16, h64, h288, h432]
    ring
  rw [← W.coe_Δ'] at hdelta
  exact Units.ne_zero W.Δ' hdelta

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

variable {F : Type u} [Field F]
/--
[degreeDataAtThree_of_pointCount_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma degreeDataAtThree_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 7) :
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 3 N) := by
  let a : ℤ := 4 - N
  have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hpos
  have hNle : (N : ℤ) ≤ 7 := by exact_mod_cast hle
  have hdisc : a ^ 2 ≤ 9 := by
    dsimp only [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNpos) (sub_nonneg.mpr hNle)]
  refine ⟨MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.ofQuadratic
    3 N a (by simp [a]) ?_ ?_⟩
  · intro n
    norm_num
    nlinarith [sq_nonneg (2 * n + a)]
  · intro n hn _
    norm_num at hn
    nlinarith [sq_nonneg (2 * n + a)]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

/--
[manin_degree_data_of_card_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
lemma manin_degree_data_of_card_eq_three
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F}
-- given
  (hF : Nat.card F = 3) :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtThree_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

/--
[hasse_bound_of_isCharNeTwoNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
lemma hasse_bound_of_isCharNeTwoNF
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharNeTwoNF] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) :=
-- proof
  (Classical.choice (manin_degree_data_of_isCharNeTwoNF W)).hasse_bound
end


/--
[manin_degree_data_of_isCharNeTwoNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma manin_degree_data_of_isCharNeTwoNF_eq
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharNeTwoNF] :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist.manin_degree_data_of_isCharNeTwoNF W


-- created on 2026-10-20
-- updated on 2026-10-26
