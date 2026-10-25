import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part10
open Polynomial WeierstrassCurve.Affine in ShortWeierstrassCurve ShortWeierstrassCurve.VeluDeg2Data ShortWeierstrassCurve.VeluOddData IsogenyStandardForm DivisionPolynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable [CommRing R] (E : ShortWeierstrassCurve R)
/--
[ψ₂_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma ψ₂_eq : E.toWeierstrassCurve.ψ₂ = C (C 2) * Y := by
  unfold WeierstrassCurve.ψ₂ WeierstrassCurve.Affine.polynomialY
  simp [toWeierstrassCurve, WeierstrassCurve.toAffine]
/-- The third division polynomial $\psi_3$ depends only on $X$ (it equals $C \, \Psi_3$). -/
@[simp] lemma divisionPoly_three :
  E.divisionPoly 3 = C E.toWeierstrassCurve.Ψ₃ :=
  E.toWeierstrassCurve.ψ_three
/-- The fourth division polynomial factors as $\psi_4 = C \, \mathrm{pre}\Psi_4 \cdot \psi_2$. -/
@[simp] lemma divisionPoly_four :
  E.divisionPoly 4 = C E.toWeierstrassCurve.preΨ₄ * E.toWeierstrassCurve.ψ₂ :=
  E.toWeierstrassCurve.ψ_four
/-- Negating the index negates the division polynomial: $\psi_{-n} = -\psi_n$. -/
@[simp] lemma divisionPoly_neg (n : ℤ) :
  E.divisionPoly (-n) = -E.divisionPoly n :=
  E.toWeierstrassCurve.ψ_neg n

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[divisionPoly_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma divisionPoly_odd
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {m : ℤ} :
-- imply
  E.divisionPoly (2 * m + 1) = E.divisionPoly (m + 2) * E.divisionPoly m ^ 3 - E.divisionPoly (m - 1) * E.divisionPoly (m + 1) ^ 3 :=
-- proof
  E.toWeierstrassCurve.ψ_odd m

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[divisionPoly_even](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma divisionPoly_even
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {m : ℤ} :
-- imply
  E.divisionPoly (2 * m) * E.toWeierstrassCurve.ψ₂ = E.divisionPoly (m - 1) ^ 2 * E.divisionPoly m * E.divisionPoly (m + 2) - E.divisionPoly (m - 2) * E.divisionPoly m * E.divisionPoly (m + 1) ^ 2 :=
-- proof
  E.toWeierstrassCurve.ψ_even m

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[phiPoly_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma phiPoly_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  E.phiPoly n = C X * E.divisionPoly n ^ 2 - E.divisionPoly (n + 1) * E.divisionPoly (n - 1) :=
-- proof
  rfl
/-- The zeroth $\phi$-polynomial is $\phi_0 = 1$. -/
@[simp] lemma phiPoly_zero : E.phiPoly 0 = 1 :=
  E.toWeierstrassCurve.φ_zero
/-- The first $\phi$-polynomial is $\phi_1 = X$. -/
@[simp] lemma phiPoly_one : E.phiPoly 1 = C X :=
  E.toWeierstrassCurve.φ_one
/-- The $\phi$-polynomial is invariant under negation of the index: $\phi_{-n} = \phi_n$. -/
@[simp] lemma phiPoly_neg (n : ℤ) : E.phiPoly (-n) = E.phiPoly n :=
  E.toWeierstrassCurve.φ_neg n

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[Psi_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma Psi_odd
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ}
-- given
  (hn : ¬Even n) :
-- imply
  E.toWeierstrassCurve.Ψ n = C (E.toWeierstrassCurve.preΨ n) := by
-- proof
  unfold WeierstrassCurve.Ψ
  rw [if_neg hn, mul_one]

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[Psi_even](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma Psi_even
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ}
-- given
  (hn : Even n) :
-- imply
  E.toWeierstrassCurve.Ψ n = C (E.toWeierstrassCurve.preΨ n) * E.toWeierstrassCurve.ψ₂ := by
-- proof
  unfold WeierstrassCurve.Ψ
  rw [if_pos hn]

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[omegaPolyNumer_mk_even](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma omegaPolyNumer_mk_even
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ}
-- given
  (hn : Even n) :
-- imply
  WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve (E.omegaPolyNumer n) = WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve (E.toWeierstrassCurve.ψ₂ * C (E.toWeierstrassCurve.preΨ (n + 2) * E.toWeierstrassCurve.preΨ (n - 1) ^ 2 - E.toWeierstrassCurve.preΨ (n - 2) * E.toWeierstrassCurve.preΨ (n + 1) ^ 2)) := by
-- proof
  simp only [omegaPolyNumer, divisionPoly, map_sub, map_mul, map_pow,
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ]
  have hn2 : Even (n + 2) := by obtain ⟨k, hk⟩ := hn; exact ⟨k + 1, by omega⟩
  have hno1 : ¬Even (n - 1) := by intro ⟨k, hk⟩; obtain ⟨m, hm⟩ := hn; omega
  have hn_2 : Even (n - 2) := by obtain ⟨k, hk⟩ := hn; exact ⟨k - 1, by omega⟩
  have hno2 : ¬Even (n + 1) := by intro ⟨k, hk⟩; obtain ⟨m, hm⟩ := hn; omega
  simp only [WeierstrassCurve.Ψ, if_pos hn2, if_neg hno1, if_pos hn_2, if_neg hno2, mul_one]
  simp only [map_mul]
  ring

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[omegaPolyNumer_mk_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma omegaPolyNumer_mk_odd
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ}
-- given
  (hn : ¬Even n) :
-- imply
  WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve (E.omegaPolyNumer n) = WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve (E.toWeierstrassCurve.ψ₂ ^ 2 * C (E.toWeierstrassCurve.preΨ (n + 2) * E.toWeierstrassCurve.preΨ (n - 1) ^ 2 - E.toWeierstrassCurve.preΨ (n - 2) * E.toWeierstrassCurve.preΨ (n + 1) ^ 2)) := by
-- proof
  simp only [omegaPolyNumer, divisionPoly, map_sub, map_mul, map_pow,
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ]
  have hno2 : ¬Even (n + 2) := by intro ⟨k, hk⟩; exact hn ⟨k - 1, by omega⟩
  have hn1 : Even (n - 1) := by
    rw [Int.not_even_iff_odd] at hn; obtain ⟨k, hk⟩ := hn; exact ⟨k, by omega⟩
  have hno_2 : ¬Even (n - 2) := by intro ⟨k, hk⟩; exact hn ⟨k + 1, by omega⟩
  have hn_1 : Even (n + 1) := by
    rw [Int.not_even_iff_odd] at hn; obtain ⟨k, hk⟩ := hn; exact ⟨k + 1, by omega⟩
  simp only [WeierstrassCurve.Ψ, if_neg hno2, if_pos hn1, if_neg hno_2, if_pos hn_1, mul_one]
  simp only [map_mul]
  ring

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[divisionPoly_neg_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma divisionPoly_neg_sq
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  E.divisionPoly (-n) ^ 2 = E.divisionPoly n ^ 2 := by
-- proof
  rw [divisionPoly_neg]; ring

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[x_coord_neg_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma x_coord_neg_invariant
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  E.phiPoly (-n) = E.phiPoly n ∧ E.divisionPoly (-n) ^ 2 = E.divisionPoly n ^ 2 :=
-- proof
  ⟨E.phiPoly_neg n, E.divisionPoly_neg_sq n⟩

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[psi_odd_verification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma psi_odd_verification
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {m : ℤ} :
-- imply
  E.phiPoly m * E.divisionPoly (m + 1) ^ 2 - E.phiPoly (m + 1) * E.divisionPoly m ^ 2 = E.divisionPoly (2 * m + 1) := by
-- proof
  have key : E.phiPoly m * E.divisionPoly (m + 1) ^ 2 -
    E.phiPoly (m + 1) * E.divisionPoly m ^ 2 =
    E.divisionPoly (m + 1 + 1) * E.divisionPoly m ^ 3 -
    E.divisionPoly (m - 1) * E.divisionPoly (m + 1) ^ 3 := by
    change (C X * E.divisionPoly m ^ 2 - E.divisionPoly (m + 1) * E.divisionPoly (m - 1)) *
      E.divisionPoly (m + 1) ^ 2 -
      (C X * E.divisionPoly (m + 1) ^ 2 -
        E.divisionPoly (m + 1 + 1) * E.divisionPoly (m + 1 - 1)) *
        E.divisionPoly m ^ 2 =
      E.divisionPoly (m + 1 + 1) * E.divisionPoly m ^ 3 -
      E.divisionPoly (m - 1) * E.divisionPoly (m + 1) ^ 3
    have h : (m + 1 - 1 : ℤ) = m := by omega
    rw [h]
    ring
  rw [key, show (m + 1 + 1 : ℤ) = m + 2 by omega]
  exact (E.divisionPoly_odd m).symm

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[psi_even_verification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma psi_even_verification
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {m : ℤ} :
-- imply
  E.divisionPoly m * E.omegaPolyNumer m = E.divisionPoly (2 * m) * E.toWeierstrassCurve.ψ₂ := by
-- proof
  unfold omegaPolyNumer
  rw [E.divisionPoly_even m]
  ring

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[Phi_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma Phi_natDegree
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  [Nontrivial R]
  {n : ℤ} :
-- imply
  (E.toWeierstrassCurve.Φ n).natDegree = n.natAbs ^ 2 :=
-- proof
  E.toWeierstrassCurve.natDegree_Φ n

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[Phi_leadingCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma Phi_leadingCoeff
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  [Nontrivial R]
  {n : ℤ} :
-- imply
  (E.toWeierstrassCurve.Φ n).leadingCoeff = 1 :=
-- proof
  E.toWeierstrassCurve.leadingCoeff_Φ n

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

variable [CommRing R] (E : ShortWeierstrassCurve R)
/--
[ΨSq_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
$(n^2 - 4)/2$ for even $n$ and $(n^2 - 1)/2$ for odd $n$. -/
lemma ΨSq_natDegree [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
  (E.toWeierstrassCurve.ΨSq n).natDegree = n.natAbs ^ 2 - 1 :=
  E.toWeierstrassCurve.natDegree_ΨSq h

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

variable [CommRing R] (E : ShortWeierstrassCurve R)
/--
[ΨSq_leadingCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma ΨSq_leadingCoeff [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
  (E.toWeierstrassCurve.ΨSq n).leadingCoeff = ↑n ^ 2 :=
  E.toWeierstrassCurve.leadingCoeff_ΨSq h

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

variable [CommRing R] (E : ShortWeierstrassCurve R)
/--
[ΨSq_leading_term](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma ΨSq_leading_term [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
  (E.toWeierstrassCurve.ΨSq n).natDegree = n.natAbs ^ 2 - 1 ∧
  (E.toWeierstrassCurve.ΨSq n).leadingCoeff = ↑n ^ 2 :=
  ⟨E.ΨSq_natDegree h, E.ΨSq_leadingCoeff h⟩

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[toWeierstrassCurve_short_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma toWeierstrassCurve_short_form
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.a₁ = 0 ∧ E.toWeierstrassCurve.a₂ = 0 ∧ E.toWeierstrassCurve.a₃ = 0 :=
-- proof
  ⟨rfl, rfl, rfl⟩
end ShortWeierstrassCurve
noncomputable section PointEval
open Polynomial WeierstrassCurve.Affine


namespace ShortWeierstrassCurve

/--
[mulByN_x_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma mulByN_x_one
  [Field F]
  [DecidableEq F]
  {E : ShortWeierstrassCurve F}
  {x₀ y₀ : F} :
-- imply
  E.mulByN_x 1 x₀ y₀ = x₀ := by
-- proof
  simp [mulByN_x]

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[four_ne_zero_of_isElliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma four_ne_zero_of_isElliptic
  [Field F]
  [DecidableEq F]
  {E : ShortWeierstrassCurve F}
  [hE : E.toWeierstrassCurve.IsElliptic] :
-- imply
  (4 : F) ≠ 0 := by
-- proof
  intro h4
  have h2 : (2 : F) = 0 :=
    pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp (by linear_combination h4)
  have hΔ : E.toWeierstrassCurve.Δ = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, toWeierstrassCurve]
    have h64 : (64 : F) = 0 := by linear_combination 32 * h2
    have h432 : (432 : F) = 0 := by linear_combination 216 * h2
    ring_nf
    rw [h432, h64]
    ring
  exact absurd hΔ (isUnit_iff_ne_zero.mp hE.isUnit)

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[evalOmegaNumer_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma evalOmegaNumer_one
  [Field F]
  [DecidableEq F]
  {E : ShortWeierstrassCurve F}
  {x₀ y₀ : F} :
-- imply
  E.evalOmegaNumer 1 x₀ y₀ = 4 * y₀ ^ 2 := by
-- proof
  simp only [evalOmegaNumer, omegaPolyNumer, Polynomial.evalBivariate, divisionPoly]
  show ((E.toWeierstrassCurve.ψ 3 * (E.toWeierstrassCurve.ψ 0) ^ 2 -
    E.toWeierstrassCurve.ψ (-1) * (E.toWeierstrassCurve.ψ 2) ^ 2).eval (C y₀)).eval x₀ =
    4 * y₀ ^ 2
  simp only [WeierstrassCurve.ψ_zero, WeierstrassCurve.ψ_neg, WeierstrassCurve.ψ_one,
    WeierstrassCurve.ψ_two]
  unfold WeierstrassCurve.ψ₂ WeierstrassCurve.Affine.polynomialY
  simp [toWeierstrassCurve, WeierstrassCurve.toAffine]
  ring

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[mulByN_y_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma mulByN_y_one
  [Field F]
  [DecidableEq F]
  {E : ShortWeierstrassCurve F}
  [E.toWeierstrassCurve.IsElliptic]
  {x₀ y₀ : F} :
-- imply
  E.mulByN_y 1 x₀ y₀ = y₀ := by
-- proof
  simp only [mulByN_y, evalOmega, evalOmegaNumer_one, evalDivisionPoly_one, one_pow, div_one]
  by_cases hy : y₀ = 0
  · simp [hy]
  · rw [div_eq_iff (mul_ne_zero (E.four_ne_zero_of_isElliptic) hy)]
    ring

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[theorem_5_21_algebraic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma theorem_5_21_algebraic
  [Field F]
  [DecidableEq F]
  {E : ShortWeierstrassCurve F}
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  (∀ n : ℤ, E.phiPoly (-n) = E.phiPoly n ∧ E.divisionPoly (-n) ^ 2 = E.divisionPoly n ^ 2) ∧ (∀ m : ℤ, E.phiPoly m * E.divisionPoly (m + 1) ^ 2 - E.phiPoly (m + 1) * E.divisionPoly m ^ 2 = E.divisionPoly (2 * m + 1)) ∧ (∀ m : ℤ, E.divisionPoly m * E.omegaPolyNumer m = E.divisionPoly (2 * m) * E.toWeierstrassCurve.ψ₂) :=
-- proof
  ⟨E.x_coord_neg_invariant, E.psi_odd_verification, E.psi_even_verification⟩
/-- Theorem 5.21: case split on whether $\psi_n(P)$ vanishes, returning either the affine
formulae for $[n] P$ or that $[n] P = O$. -/
end ShortWeierstrassCurve
end PointEval
universe uSWC
/-- Auxiliary lemma for the coprimality of $\Phi_n$ and $\Psi_n^2$: a common root would
witness an affine $n$-torsion point that is also $(n \pm 1)$-torsion, contradicting
nontriviality. -/
namespace ShortWeierstrassCurve
variable {k : Type uSWC} [Field k] (E : ShortWeierstrassCurve k)
open WeierstrassCurve.Affine in
/-- The polynomials $\Phi_n$ and $\Psi_n^2$ are coprime over an elliptic short Weierstrass
curve, used to extract the multiplication-by-$n$ map as a standard-form isogeny. -/
end ShortWeierstrassCurve
namespace ShortWeierstrassCurve

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[t_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma t_eq
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E} :
-- imply
  d.t = 3 * d.x₀ ^ 2 + E.A :=
-- proof
  rfl

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[w_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma w_eq
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E} :
-- imply
  d.w = d.x₀ * (3 * d.x₀ ^ 2 + E.A) :=
-- proof
  rfl

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[kernel_point_on_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma kernel_point_on_curve
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E} :
-- imply
  d.x₀ ^ 3 + E.A * d.x₀ + E.B = 0 :=
-- proof
  d.root_eq

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_image_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_image_identity
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  {x : k} :
-- imply
  (x ^ 2 - d.x₀ * x + d.t) ^ 3 + d.A' * (x ^ 2 - d.x₀ * x + d.t) * (x - d.x₀) ^ 2 + d.B' * (x - d.x₀) ^ 3 = ((x - d.x₀) ^ 2 - d.t) ^ 2 * (x ^ 2 + d.x₀ * x + d.x₀ ^ 2 + E.A) := by
-- proof
  simp only [t, w, A', B']
  linear_combination (x - d.x₀) ^ 3 * d.root_eq

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_u_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_u_natDegree
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E} :
-- imply
  (X ^ 2 - C d.x₀ * X + C d.t : F[X]).natDegree = 2 := by
-- proof
  have h1 : (C d.x₀ * X : F[X]).natDegree ≤ 1 := by
    calc (C d.x₀ * X : F[X]).natDegree
      ≤ (C d.x₀ : F[X]).natDegree + X.natDegree := natDegree_mul_le
      _ = 0 + 1 := by simp [natDegree_C, natDegree_X]
      _ = 1 := by omega
  have h2 : (X ^ 2 - C d.x₀ * X : F[X]).natDegree = 2 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · rw [natDegree_pow, natDegree_X]
    · rw [natDegree_pow, natDegree_X]; omega
  conv_lhs =>
    rw [show X ^ 2 - C d.x₀ * X + C d.t = (X ^ 2 - C d.x₀ * X) + C d.t from by ring]
  rwa [natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_C, h2]; omega)]

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_wronskian_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_wronskian_eq
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E} :
-- imply
  Polynomial.derivative (X ^ 2 - C d.x₀ * X + C d.t : F[X]) * (X - C d.x₀) - (X ^ 2 - C d.x₀ * X + C d.t) * Polynomial.derivative (X - C d.x₀) = (X - C d.x₀) ^ 2 - C d.t := by
-- proof
  simp only [derivative_sub, derivative_add, derivative_pow, derivative_mul, derivative_C,
    derivative_X, map_ofNat, Nat.cast_ofNat, mul_one, zero_mul, sub_zero, zero_add]
  ring

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_deg2_is_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_deg2_is_separable
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E} :
-- imply
  Polynomial.derivative (X ^ 2 - C d.x₀ * X + C d.t : F[X]) * (X - C d.x₀) - (X ^ 2 - C d.x₀ * X + C d.t) * Polynomial.derivative (X - C d.x₀) ≠ 0 := by
-- proof
  rw [d.velu_wronskian_eq]
  have h2 : ((X - C d.x₀ : F[X]) ^ 2).natDegree = 2 := by
    rw [natDegree_pow, natDegree_X_sub_C]
  have h4 : (C d.t : F[X]).natDegree < ((X - C d.x₀ : F[X]) ^ 2).natDegree := by
    rw [h2, natDegree_C]; omega
  have h6 : ((X - C d.x₀ : F[X]) ^ 2 - C d.t).natDegree = 2 :=
    (natDegree_sub_eq_left_of_natDegree_lt h4).trans h2
  intro h
  rw [h] at h6; simp at h6

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_deg2_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_deg2_degree_eq_two
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E} :
-- imply
  max (X ^ 2 - C d.x₀ * X + C d.t : F[X]).natDegree (X - C d.x₀ : F[X]).natDegree = 2 := by
-- proof
  rw [d.velu_u_natDegree, natDegree_X_sub_C]; omega

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_deg2_kernel_on_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_deg2_kernel_on_curve
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E} :
-- imply
  (0 : F) ^ 2 = d.x₀ ^ 3 + E.A * d.x₀ + E.B := by
-- proof
  rw [d.root_eq]; ring

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_deg2_kernel_denom_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_deg2_kernel_denom_vanish
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E} :
-- imply
  d.phi_x_denom d.x₀ = 0 ∧ d.phi_y_denom d.x₀ = 0 := by
-- proof
  constructor
  · exact sub_self d.x₀
  · simp [phi_y_denom, sub_self]

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_deg2_kernel_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_deg2_kernel_unique
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E}
  {x : F}
-- given
  (hx : x ≠ d.x₀) :
-- imply
  d.phi_x_denom x ≠ 0 :=
-- proof
  sub_ne_zero.mpr hx

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_y_sq_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_y_sq_factor
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E}
  {x y : F}
-- given
  (hcurve : y ^ 2 = x ^ 3 + E.A * x + E.B) :
-- imply
  y ^ 2 = (x - d.x₀) * (x ^ 2 + d.x₀ * x + d.x₀ ^ 2 + E.A) := by
-- proof
  rw [hcurve]; linear_combination d.root_eq

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_phi_maps_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_phi_maps_points
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E}
  {x y : F}
-- given
  (hcurve : y ^ 2 = x ^ 3 + E.A * x + E.B) :
-- imply
  ((x - d.x₀) ^ 2 - d.t) ^ 2 * y ^ 2 = (x - d.x₀) * ((x ^ 2 - d.x₀ * x + d.t) ^ 3 + d.A' * (x ^ 2 - d.x₀ * x + d.t) * (x - d.x₀) ^ 2 + d.B' * (x - d.x₀) ^ 3) := by
-- proof
  rw [d.velu_y_sq_factor hcurve]
  rw [mul_left_comm]
  congr 1
  exact (d.velu_image_identity x).symm

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve.VeluDeg2Data

/--
[velu_deg2_is_standard_form_separable_deg2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma velu_deg2_is_standard_form_separable_deg2
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E}
  [Field F]
  {E : ShortWeierstrassCurve F}
  {d : VeluDeg2Data E} :
-- imply
  (max (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X + Polynomial.C d.t : F[X]).natDegree (Polynomial.X - Polynomial.C d.x₀ : F[X]).natDegree = 2) ∧ (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X + Polynomial.C d.t : F[X]) * (Polynomial.X - Polynomial.C d.x₀) - (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X + Polynomial.C d.t) * Polynomial.derivative (Polynomial.X - Polynomial.C d.x₀) ≠ 0) :=
-- proof
  ⟨d.velu_deg2_degree_eq_two, d.velu_deg2_is_separable⟩

end ShortWeierstrassCurve.VeluDeg2Data

namespace ShortWeierstrassCurve

/--
[AffinePoint.wQ_expanded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma AffinePoint.wQ_expanded
  [CommRing k]
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.wQ = 2 * Q.y ^ 2 + (3 * Q.x ^ 2 + E.A) * Q.x :=
-- proof
  rfl

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[AffinePoint.uQ_eq_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma AffinePoint.uQ_eq_curve
  [CommRing k]
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.uQ = 2 * (Q.x ^ 3 + E.A * Q.x + E.B) := by
-- proof
  simp only [AffinePoint.uQ]
  linear_combination 2 * Q.on_curve

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[AffinePoint.wQ_eq_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma AffinePoint.wQ_eq_curve
  [CommRing k]
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.wQ = 5 * Q.x ^ 3 + 3 * E.A * Q.x + 2 * E.B := by
-- proof
  simp only [AffinePoint.wQ, AffinePoint.uQ, AffinePoint.tQ]
  linear_combination 2 * Q.on_curve

end ShortWeierstrassCurve

/--
[corollary_5_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma corollary_5_2
  [Field F]
  [CharZero F]
  {α : IsogenyStandardForm F}
-- given
  (hdeg : 0 < α.degree) :
-- imply
  α.IsSeparable := by
-- proof
  rw [IsogenyStandardForm.IsSeparable]
  intro h
  have hwronskian : α.u.wronskian α.v = 0 := by
    simp only [Polynomial.wronskian]
    linear_combination -h
  have ⟨hu', hv'⟩ := (lemma_5_1_first_iff α.coprime_uv).mp hwronskian
  have hu_const : α.u.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hu'
  have hv_const : α.v.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hv'
  have hdeg_zero : α.degree = 0 := by
    simp [IsogenyStandardForm.degree, hu_const, hv_const]
  omega

namespace IsogenyStandardForm

/--
[frobeniusFactorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma frobeniusFactorization
  [Field F]
  {p : ℕ}
  [CharP F p]
  {α : IsogenyStandardForm F}
-- given
  (hp : Nat.Prime p)
  (hdeg : 0 < α.degree) :
-- imply
  ∃ (α_sep : IsogenyStandardForm F) (n : ℕ), α_sep.IsSeparable ∧ α.u = Polynomial.expand F (p ^ n) α_sep.u ∧ α.v = Polynomial.expand F (p ^ n) α_sep.v ∧ α.degree = p ^ n * α_sep.degree := by
-- proof
  have hfact : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_ne : p ≠ 0 := hp.ne_zero
  suffices ∀ (d : ℕ) (α : IsogenyStandardForm F),
    α.degree = d → 0 < d →
    ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
      α_sep.IsSeparable ∧
      α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
      α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
      α.degree = p ^ n * α_sep.degree by
    exact this α.degree α rfl hdeg
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro α hd hdeg_pos
  by_cases hsep : α.IsSeparable
  · exact ⟨α, 0, hsep,
    by simp [Polynomial.expand_one],
    by simp [Polynomial.expand_one],
    by simp⟩
  ·
    rw [IsogenyStandardForm.IsSeparable] at hsep
    push Not at hsep
    have hinsep : Polynomial.derivative α.u * α.v - α.u * Polynomial.derivative α.v = 0 := hsep
    obtain ⟨u₁, v₁, hu₁, hv₁⟩ := lemma_5_3_x (show p ≠ 0 from hp_ne) α.coprime_uv hinsep
    have hcop₁ : IsCoprime u₁ v₁ := by
      rwa [← (Polynomial.isCoprime_expand hp_ne (f := u₁) (g := v₁)), hu₁, hv₁]
    have hv₁_ne : v₁ ≠ 0 := by
      intro habs; rw [habs, map_zero] at hv₁; exact α.v_ne_zero hv₁.symm
    have hdeg_u₁ : α.u.natDegree = u₁.natDegree * p := by
      rw [← hu₁, Polynomial.natDegree_expand]
    have hdeg_v₁ : α.v.natDegree = v₁.natDegree * p := by
      rw [← hv₁, Polynomial.natDegree_expand]
    let α₁ : IsogenyStandardForm F :=
      ⟨u₁, v₁, α.s, α.t, hv₁_ne, α.t_ne_zero, hcop₁, α.coprime_st⟩
    have hdeg_α₁ : α₁.degree * p = α.degree := by
      unfold IsogenyStandardForm.degree
      simp only [α₁]
      rw [hdeg_u₁, hdeg_v₁]
      obtain h | h := le_or_gt u₁.natDegree v₁.natDegree
      · rw [max_eq_right (Nat.mul_le_mul_right p h), max_eq_right h]
      · rw [max_eq_left (Nat.mul_le_mul_right p (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h))),
        max_eq_left (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h))]
    have hdeg_α₁_pos : 0 < α₁.degree := by
      by_contra h
      push Not at h
      interval_cases α₁.degree
      simp at hdeg_α₁; omega
    have hdeg_lt : α₁.degree < d := by
      have heq : α₁.degree * p = d := by omega
      nlinarith [hp.one_lt]
    obtain ⟨α_sep, m, hsep_m, hu_m, hv_m, hdeg_m⟩ :=
      ih α₁.degree hdeg_lt α₁ rfl hdeg_α₁_pos
    have hu₁_eq : u₁ = (Polynomial.expand F (p ^ m)) α_sep.u := hu_m
    have hv₁_eq : v₁ = (Polynomial.expand F (p ^ m)) α_sep.v := hv_m
    refine ⟨α_sep, m + 1, hsep_m, ?_, ?_, ?_⟩
    ·
      rw [show p ^ (m + 1) = p ^ m * p from pow_succ p m]
      rw [← hu₁, hu₁_eq, Polynomial.expand_expand, Nat.mul_comm]
    · rw [show p ^ (m + 1) = p ^ m * p from pow_succ p m]
      rw [← hv₁, hv₁_eq, Polynomial.expand_expand, Nat.mul_comm]
    ·
      rw [show p ^ (m + 1) = p ^ m * p from pow_succ p m,
        show p ^ m * p * α_sep.degree = α₁.degree * p by rw [hdeg_m]; ring,
        hdeg_α₁]
end IsogenyStandardForm


namespace ShortWeierstrassCurve

/--
[derivative_Phi_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma derivative_Phi_ne_zero
  {k : Type uSWC}
  [Field k]
  {E : ShortWeierstrassCurve k}
  {n : ℤ}
-- given
  (hn : (n : k) ≠ 0) :
-- imply
  Polynomial.derivative (E.toWeierstrassCurve.Φ n) ≠ 0 := by
-- proof
  intro hd
  have h_deg := E.toWeierstrassCurve.natDegree_Φ n
  have h_lc := E.toWeierstrassCurve.leadingCoeff_Φ n
  have h_nabs : n.natAbs ≠ 0 := by
    intro h; exact hn (by simp [Int.natAbs_eq_zero.mp h])
  have h_pos : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow 2 n.natAbs (Nat.pos_of_ne_zero h_nabs)
  have h_coeff : Polynomial.coeff (Polynomial.derivative (E.toWeierstrassCurve.Φ n))
    ((E.toWeierstrassCurve.Φ n).natDegree - 1) = 0 := by
    rw [hd]; simp
  rw [Polynomial.coeff_derivative] at h_coeff
  have hsub1 : (E.toWeierstrassCurve.Φ n).natDegree - 1 + 1 =
    (E.toWeierstrassCurve.Φ n).natDegree := by rw [h_deg]; omega
  rw [hsub1, Polynomial.coeff_natDegree, h_lc, one_mul, h_deg] at h_coeff
  set m := n.natAbs ^ 2 - 1 with hm_def
  have hm_succ : m + 1 = n.natAbs ^ 2 := by omega
  have h_zero : (↑(n.natAbs ^ 2) : k) = 0 := by
    rw [← hm_succ, Nat.cast_add, Nat.cast_one]; exact h_coeff
  have h_sq : (n : k) ^ 2 = (↑(n.natAbs) : k) ^ 2 := by
    have h : (n : ℤ) ^ 2 = (↑(n.natAbs) : ℤ) ^ 2 := by simp
    have h2 := congr_arg (Int.cast : ℤ → k) h
    push_cast at h2; rw [Int.abs_eq_natAbs] at h2; norm_cast at h2 ⊢
  have : (n : k) ^ 2 = 0 := by rw [h_sq, ← Nat.cast_pow]; exact h_zero
  exact pow_ne_zero 2 hn this

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[theorem_5_25_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma theorem_5_25_degree
  {k : Type uSWC}
  [Field k]
  {E : ShortWeierstrassCurve k}
  [E.toWeierstrassCurve.IsElliptic]
  {n : ℤ}
-- given
  (hn : (n : k) ≠ 0) :
-- imply
  (E.mulByNStandardForm hn).degree = n.natAbs ^ 2 := by
-- proof
  simp only [mulByNStandardForm, IsogenyStandardForm.degree]
  rw [E.toWeierstrassCurve.natDegree_Φ n, E.toWeierstrassCurve.natDegree_ΨSq hn]
  have : 1 ≤ n.natAbs ^ 2 := by
    have : n.natAbs ≠ 0 := by intro h; exact hn (by simp [Int.natAbs_eq_zero.mp h])
    exact Nat.one_le_pow 2 n.natAbs (Nat.pos_of_ne_zero this)
  omega

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[theorem_5_25_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma theorem_5_25_separable
  {k : Type uSWC}
  [Field k]
  {E : ShortWeierstrassCurve k}
  [E.toWeierstrassCurve.IsElliptic]
  {n : ℤ}
-- given
  (hn : (n : k) ≠ 0) :
-- imply
  (E.mulByNStandardForm hn).IsSeparable := by
-- proof
  simp only [IsogenyStandardForm.IsSeparable, mulByNStandardForm]
  intro h_insep
  have h_wron : (E.toWeierstrassCurve.Φ n).wronskian (E.toWeierstrassCurve.ΨSq n) = 0 := by
    simp only [Polynomial.wronskian]; linear_combination -h_insep
  have ⟨hd_Phi, _⟩ := (lemma_5_1_first_iff (E.Phi_ΨSq_isCoprime n)).mp h_wron
  exact E.derivative_Phi_ne_zero hn hd_Phi

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

/--
[theorem_5_25_degree_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma theorem_5_25_degree_general
  {k : Type uSWC}
  [Field k]
  {E : ShortWeierstrassCurve k}
  {n : ℤ}
-- given
  (hn : n ≠ 0) :
-- imply
  max (E.toWeierstrassCurve.Φ n).natDegree (E.toWeierstrassCurve.ΨSq n).natDegree = n.natAbs ^ 2 := by
-- proof
  rw [E.toWeierstrassCurve.natDegree_Φ n]
  have hle : (E.toWeierstrassCurve.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 :=
    E.toWeierstrassCurve.natDegree_ΨSq_le n
  have h1 : 1 ≤ n.natAbs ^ 2 := by
    have : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
    calc 1 = 1 ^ 2 := by ring
    _ ≤ n.natAbs ^ 2 := Nat.pow_le_pow_left this 2
  omega
/-- Theorem 5.25 (combined): for nonzero $n$, $[n]$ has degree $n^2$ and is separable iff
$n \neq 0$ in $k$. -/
end ShortWeierstrassCurve


namespace IsogenyStandardForm

/--
[exists_separableDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma exists_separableDegree
  [Field F]
  {p : ℕ}
  [CharP F p]
  {α : IsogenyStandardForm F}
-- given
  (hp : Nat.Prime p)
  (hdeg : 0 < α.degree) :
-- imply
  ∃ d, α.HasSeparableDegree hp d := by
-- proof
  obtain ⟨α_sep, n, hsep, hu, hv, _⟩ := frobeniusFactorization hp α hdeg
  exact ⟨α_sep.degree, α_sep, n, hsep, hu, hv, rfl⟩

end IsogenyStandardForm

namespace IsogenyStandardForm

/--
[degree_eq_insep_mul_sep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma degree_eq_insep_mul_sep
  [Field F]
  {p : ℕ}
  [CharP F p]
  {α : IsogenyStandardForm F}
  {d : ℕ}
-- given
  (_hp : Nat.Prime p)
  (_hdeg : 0 < α.degree)
  (hs : α.HasSeparableDegree _hp d) :
-- imply
  ∃ n, α.degree = p ^ n * d := by
-- proof
  obtain ⟨α_sep, n, _, hu, hv, hd⟩ := hs
  refine ⟨n, ?_⟩
  subst hd
  unfold degree
  rw [hu, hv, Polynomial.natDegree_expand, Polynomial.natDegree_expand]
  obtain h | h := le_or_gt α_sep.u.natDegree α_sep.v.natDegree
  · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_right _ h), Nat.mul_comm]
  · rw [max_eq_left (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h)),
    max_eq_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h))),
    Nat.mul_comm]
end IsogenyStandardForm
namespace IsogenyStandardForm

end IsogenyStandardForm

/--
[corollary_5_9](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma corollary_5_9
  [Field F]
  {p : ℕ}
  [CharP F p]
  {α : IsogenyStandardForm F}
  {α_sep : IsogenyStandardForm F}
  {n : ℕ}
-- given
  (hp : Nat.Prime p)
  (_hdeg : 0 < α.degree)
  (_hsep : α_sep.IsSeparable)
  (hu : α.u = Polynomial.expand F (p ^ n) α_sep.u)
  (hv : α.v = Polynomial.expand F (p ^ n) α_sep.v)
  (hpure : α_sep.degree = 1) :
-- imply
  α.kernelSize = 1 := by
-- proof
  haveI : ExpChar F p := ExpChar.prime hp
  show max α.u.natSepDegree α.v.natSepDegree = 1
  rw [hu, hv, Polynomial.natSepDegree_expand _ p, Polynomial.natSepDegree_expand _ p]
  have hu_le := Polynomial.natSepDegree_le_natDegree α_sep.u
  have hv_le := Polynomial.natSepDegree_le_natDegree α_sep.v
  unfold IsogenyStandardForm.degree at hpure
  obtain huv | huv := le_or_gt α_sep.u.natDegree α_sep.v.natDegree
  · rw [max_eq_right huv] at hpure
    have := Polynomial.natSepDegree_ne_zero α_sep.v (by omega)
    omega
  · rw [max_eq_left (le_of_lt huv)] at hpure
    have := Polynomial.natSepDegree_ne_zero α_sep.u (by omega)
    omega

/--
[corollary_5_9'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma corollary_5_9'
  [Field F]
  {p : ℕ}
  [CharP F p]
  {α : IsogenyStandardForm F}
-- given
  (hp : Nat.Prime p)
  (hdeg : 0 < α.degree)
  (hpure : α.IsPurelyInseparable' hp) :
-- imply
  α.kernelSize = 1 := by
-- proof
  obtain ⟨α_sep, n, hsep, hu, hv, hd⟩ := hpure
  exact corollary_5_9 hp α hdeg α_sep n hsep hu hv hd
/-- Converse direction: if $\alpha$ has kernel size $1$ then it is purely inseparable. -/
namespace IsogenyStandardForm
variable {F : Type*} [Field F]
open Polynomial

namespace IsogenyStandardForm

/--
[HasSeparableDegree.insepDegree_and_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma HasSeparableDegree.insepDegree_and_factorization
  [Field F]
  {p : ℕ}
  [CharP F p]
  {α : IsogenyStandardForm F}
  {d : ℕ}
-- given
  (hp : Nat.Prime p)
  (hs : α.HasSeparableDegree hp d) :
-- imply
  ∃ n, α.HasInseparableDegree hp (p ^ n) ∧ α.degree = p ^ n * d := by
-- proof
  obtain ⟨α_sep, n, hsep, hu, hv, hd⟩ := hs
  refine ⟨n, ⟨α_sep, n, hsep, hu, hv, rfl⟩, ?_⟩
  subst hd
  unfold degree
  rw [hu, hv, Polynomial.natDegree_expand, Polynomial.natDegree_expand]
  obtain h | h := le_or_gt α_sep.u.natDegree α_sep.v.natDegree
  · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_right _ h), Nat.mul_comm]
  · rw [max_eq_left (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h)),
    max_eq_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h))),
    Nat.mul_comm]

end IsogenyStandardForm

/--
[Isogeny.exists_separable_of_finite_subgroup_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma Isogeny.exists_separable_of_finite_subgroup_unique
  {F : Type uSWC}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {G : AddSubgroup E.Point}
  [Finite G]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {φ : Isogeny E E₁}
  {ψ : Isogeny E E₂}
-- given
  (hφ : φ.toAddMonoidHom.ker = G)
  (hψ : ψ.toAddMonoidHom.ker = G) :
-- imply
  ∃ (ι : Isogeny E₁ E₂), ι.degree = 1 ∧ ∀ P, ψ P = ι (φ P) := by
-- proof
  have hle : φ.toAddMonoidHom.ker ≤ ψ.toAddMonoidHom.ker := by rw [hφ, hψ]
  let ι_hom := AddMonoidHom.liftOfSurjective φ.toAddMonoidHom φ.surjective
    ⟨ψ.toAddMonoidHom, hle⟩
  have ι_surj : Function.Surjective ι_hom := by
    intro Q
    obtain ⟨P, hP⟩ := ψ.surjective Q
    exact ⟨φ P, by simp [ι_hom, AddMonoidHom.liftOfSurjective, hP]⟩
  refine ⟨⟨ι_hom, ι_surj, 1, Nat.one_pos⟩, rfl, ?_⟩
  intro P
  show ψ.toAddMonoidHom P = ι_hom (φ.toAddMonoidHom P)
  simp [ι_hom, AddMonoidHom.liftOfSurjective]

/--
[isogeny_prime_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma isogeny_prime_factor
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {p : ℕ}
-- given
  (hdeg : 1 < α.degree)
  (hp : Nat.Prime p)
  (hdvd : p ∣ α.degree) :
-- imply
  ∃ (E_mid : WeierstrassCurve.Affine F) (β : Isogeny E₁ E_mid) (γ : Isogeny E_mid E₂), β.degree = p ∧ 0 < γ.degree ∧ γ.degree * β.degree = α.degree ∧ γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom :=
-- proof
  Isogeny.prime_factor_aux α hdeg p hp hdvd

/--
[isogeny_prime_degree_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma isogeny_prime_degree_decomposition
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
-- given
  (hdeg : 1 < α.degree) :
-- imply
  ∃ (chain : IsogenyChain E₁ E₂), chain.allPrimeDegree ∧ chain.compose = α.toAddMonoidHom := by
-- proof
  suffices ∀ (d : ℕ) {E₁ E₂ : WeierstrassCurve.Affine F} (α : Isogeny E₁ E₂),
    α.degree = d → 1 < d →
    ∃ (chain : IsogenyChain E₁ E₂),
      chain.allPrimeDegree ∧
      chain.compose = α.toAddMonoidHom by
    exact this α.degree α rfl hdeg
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro E₁' E₂' α' hαd hd
  have ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  rw [← hαd] at hdvd
  have hα_gt1 : 1 < α'.degree := by omega
  obtain ⟨E_mid, β, γ, hβ_deg, hγ_pos, hcomp_deg, hcomp_eq⟩ :=
    isogeny_prime_factor α' hα_gt1 p hp hdvd
  by_cases hγ1 : γ.degree ≤ 1
  · have hγ_deg_one : γ.degree = 1 := by omega
    have hα_is_p : α'.degree = p := by
      have : γ.degree * β.degree = α'.degree := hcomp_deg
      rw [hγ_deg_one, one_mul, hβ_deg] at this; exact this.symm
    exact ⟨.single α',
      by rw [IsogenyChain.allPrimeDegree, hα_is_p]; exact hp,
      by simp [IsogenyChain.compose]⟩
  · push_neg at hγ1
    have hγ_lt : γ.degree < d := by
      rw [← hαd]; have : γ.degree * β.degree = α'.degree := hcomp_deg
      rw [← this, hβ_deg]; nlinarith [hp.two_le]
    obtain ⟨chain_γ, hchain_γ, hcompose_γ⟩ := ih γ.degree hγ_lt γ rfl hγ1
    exact ⟨.cons β chain_γ,
      ⟨by rw [hβ_deg]; exact hp, hchain_γ⟩,
      by simp [IsogenyChain.compose, hcompose_γ, hcomp_eq]⟩
namespace DivisionPolynomial
open Polynomial WeierstrassCurve.Affine

namespace DivisionPolynomial

/--
[phi_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma phi_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  phi E n = C X * psi E n ^ 2 - psi E (n + 1) * psi E (n - 1) :=
-- proof
  E.phiPoly_eq n

end DivisionPolynomial

namespace DivisionPolynomial

/--
[psi_odd_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma psi_odd_recurrence
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {m : ℤ} :
-- imply
  psi E (2 * m + 1) = psi E (m + 2) * psi E m ^ 3 - psi E (m - 1) * psi E (m + 1) ^ 3 :=
-- proof
  E.divisionPoly_odd m

end DivisionPolynomial

namespace DivisionPolynomial

/--
[psi_even_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma psi_even_recurrence
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {m : ℤ} :
-- imply
  psi E (2 * m) * E.toWeierstrassCurve.ψ₂ = psi E (m - 1) ^ 2 * psi E m * psi E (m + 2) - psi E (m - 2) * psi E m * psi E (m + 1) ^ 2 :=
-- proof
  E.divisionPoly_even m

end DivisionPolynomial

namespace DivisionPolynomial

/--
[psi_odd_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma psi_odd_identity
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {m : ℤ} :
-- imply
  phi E m * psi E (m + 1) ^ 2 - phi E (m + 1) * psi E m ^ 2 = psi E (2 * m + 1) :=
-- proof
  E.psi_odd_verification m

end DivisionPolynomial

namespace DivisionPolynomial

/--
[psi_even_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma psi_even_identity
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {m : ℤ} :
-- imply
  psi E m * omegaNumer E m = psi E (2 * m) * E.toWeierstrassCurve.ψ₂ :=
-- proof
  E.psi_even_verification m

end DivisionPolynomial

namespace DivisionPolynomial

/--
[x_coord_neg_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma x_coord_neg_symmetry
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  phi E (-n) = phi E n ∧ psi E (-n) ^ 2 = psi E n ^ 2 :=
-- proof
  E.x_coord_neg_invariant n

end DivisionPolynomial

namespace DivisionPolynomial

/--
[theorem_5_21](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
lemma theorem_5_21
  [Field F]
  [DecidableEq F]
  {E : ShortWeierstrassCurve F}
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  (∀ n : ℤ, phi E (-n) = phi E n ∧ psi E (-n) ^ 2 = psi E n ^ 2) ∧ (∀ m : ℤ, phi E m * psi E (m + 1) ^ 2 - phi E (m + 1) * psi E m ^ 2 = psi E (2 * m + 1)) ∧ (∀ m : ℤ, psi E m * omegaNumer E m = psi E (2 * m) * E.toWeierstrassCurve.ψ₂) :=
-- proof
  E.theorem_5_21_algebraic
/-- Combined point-multiplication theorem: either $\psi_n(P) \neq 0$ and $[n]P$ is given by
the division polynomial formulae, or $\psi_n(P) = 0$ and $[n] P = O$. -/

end DivisionPolynomial

/--
[toWeierstrassCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma toWeierstrassCurve_a_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.a₁ = 0 := by
-- proof
  apply ShortWeierstrassCurve.toWeierstrassCurve_a E

/--
[toWeierstrassCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma toWeierstrassCurve_a_eq_2
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.a₂ = 0 := by
-- proof
  apply ShortWeierstrassCurve.toWeierstrassCurve_a E

/--
[toWeierstrassCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma toWeierstrassCurve_a_eq_3
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.a₃ = 0 := by
-- proof
  apply ShortWeierstrassCurve.toWeierstrassCurve_a E

/--
[toWeierstrassCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma toWeierstrassCurve_a_eq_4
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.a₄ = E.A := by
-- proof
  apply ShortWeierstrassCurve.toWeierstrassCurve_a E

/--
[toWeierstrassCurve_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma toWeierstrassCurve_a_eq_5
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.a₆ = E.B := by
-- proof
  apply ShortWeierstrassCurve.toWeierstrassCurve_a E

/--
[b](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma b_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.b₂ = 0 := by
-- proof
  apply ShortWeierstrassCurve.b E

/--
[b](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma b_eq_2
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.b₄ = 2 * E.A := by
-- proof
  apply ShortWeierstrassCurve.b E

/--
[b](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma b_eq_3
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.b₆ = 4 * E.B := by
-- proof
  apply ShortWeierstrassCurve.b E

/--
[b](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma b_eq_4
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.toWeierstrassCurve.b₈ = -(E.A ^ 2) := by
-- proof
  apply ShortWeierstrassCurve.b E

/--
[divisionPoly_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma divisionPoly_zero_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.divisionPoly 0 = 0 := by
-- proof
  apply ShortWeierstrassCurve.divisionPoly_zero E

/--
[divisionPoly_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma divisionPoly_one_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.divisionPoly 1 = 1 := by
-- proof
  apply ShortWeierstrassCurve.divisionPoly_one E

/--
[divisionPoly_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma divisionPoly_two_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.divisionPoly 2 = E.toWeierstrassCurve.ψ₂ := by
-- proof
  apply ShortWeierstrassCurve.divisionPoly_two E

/--
[divisionPoly_three](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma divisionPoly_three_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.divisionPoly 3 = C E.toWeierstrassCurve.Ψ₃ := by
-- proof
  apply ShortWeierstrassCurve.divisionPoly_three E

/--
[divisionPoly_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma divisionPoly_four_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.divisionPoly 4 = C E.toWeierstrassCurve.preΨ₄ * E.toWeierstrassCurve.ψ₂ := by
-- proof
  apply ShortWeierstrassCurve.divisionPoly_four E

/--
[divisionPoly_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma divisionPoly_neg_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  E.divisionPoly (-n) = -E.divisionPoly n := by
-- proof
  apply ShortWeierstrassCurve.divisionPoly_neg E n

/--
[phiPoly_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma phiPoly_zero_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.phiPoly 0 = 1 := by
-- proof
  apply ShortWeierstrassCurve.phiPoly_zero E

/--
[phiPoly_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma phiPoly_one_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  E.phiPoly 1 = C X := by
-- proof
  apply ShortWeierstrassCurve.phiPoly_one E

/--
[phiPoly_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma phiPoly_neg_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  E.phiPoly (-n) = E.phiPoly n := by
-- proof
  apply ShortWeierstrassCurve.phiPoly_neg E n

/--
[evalDivisionPoly_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma evalDivisionPoly_one_eq
  [Field F]
  [DecidableEq F]
  {E : ShortWeierstrassCurve F}
  {x₀ y₀ : F} :
-- imply
  E.evalDivisionPoly 1 x₀ y₀ = 1 := by
-- proof
  apply ShortWeierstrassCurve.evalDivisionPoly_one E x₀ y₀

/--
[evalPhiPoly_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma evalPhiPoly_one_eq
  [Field F]
  [DecidableEq F]
  {E : ShortWeierstrassCurve F}
  {x₀ y₀ : F} :
-- imply
  E.evalPhiPoly 1 x₀ y₀ = x₀ := by
-- proof
  apply ShortWeierstrassCurve.evalPhiPoly_one E x₀ y₀

/--
[imageCurve_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma imageCurve_A_eq
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E} :
-- imply
  d.imageCurve.A = d.A' := by
-- proof
  apply ShortWeierstrassCurve.VeluDeg2Data.imageCurve_A d

/--
[imageCurve_B](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma imageCurve_B_eq
  [CommRing k]
  {E : ShortWeierstrassCurve k}
  {d : VeluDeg2Data E} :
-- imply
  d.imageCurve.B = d.B' := by
-- proof
  apply ShortWeierstrassCurve.VeluDeg2Data.imageCurve_B d

/--
[AffinePoint.tQ_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma tQ_val_eq
  [CommRing k]
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.tQ = 3 * Q.x ^ 2 + E.A := by
-- proof
  apply ShortWeierstrassCurve.AffinePoint.tQ_val Q

/--
[AffinePoint.uQ_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma uQ_val_eq
  [CommRing k]
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.uQ = 2 * Q.y ^ 2 := by
-- proof
  apply ShortWeierstrassCurve.AffinePoint.uQ_val Q

/--
[AffinePoint.wQ_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma wQ_val_eq
  [CommRing k]
  [Field k]
  {E : ShortWeierstrassCurve k}
  {Q : AffinePoint E} :
-- imply
  Q.wQ = Q.uQ + Q.tQ * Q.x := by
-- proof
  apply ShortWeierstrassCurve.AffinePoint.wQ_val Q

/--
[imageCurve_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma imageCurve_A_eq_2
  [CommRing k]
  [Field k]
  {E : ShortWeierstrassCurve k}
  {d : VeluOddData E} :
-- imply
  d.imageCurve.A = d.A' := by
-- proof
  apply ShortWeierstrassCurve.VeluOddData.imageCurve_A d

/--
[imageCurve_B](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma imageCurve_B_eq_2
  [CommRing k]
  [Field k]
  {E : ShortWeierstrassCurve k}
  {d : VeluOddData E} :
-- imply
  d.imageCurve.B = d.B' := by
-- proof
  apply ShortWeierstrassCurve.VeluOddData.imageCurve_B d

/--
[psi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma psi_zero_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  psi E 0 = 0 := by
-- proof
  apply DivisionPolynomial.psi_zero E

/--
[psi_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma psi_one_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  psi E 1 = 1 := by
-- proof
  apply DivisionPolynomial.psi_one E

/--
[psi_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma psi_neg_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  psi E (-n) = -psi E n := by
-- proof
  apply DivisionPolynomial.psi_neg E n

/--
[phi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma phi_zero_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  phi E 0 = 1 := by
-- proof
  apply DivisionPolynomial.phi_zero E

/--
[phi_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma phi_one_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R} :
-- imply
  phi E 1 = C X := by
-- proof
  apply DivisionPolynomial.phi_one E

/--
[phi_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean)
-/
@[path]
private lemma phi_neg_eq
  [CommRing R]
  {E : ShortWeierstrassCurve R}
  {n : ℤ} :
-- imply
  phi E (-n) = phi E n := by
-- proof
  apply DivisionPolynomial.phi_neg E n


-- created on 2026-10-23
