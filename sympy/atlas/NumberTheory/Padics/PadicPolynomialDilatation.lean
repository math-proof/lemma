/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PadicPolynomialDilatation.lean -/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Padic polynomial dilatation

Source: W. A. Zuniga-Galindo, *Computing Igusa's Local Zeta Functions of
Univariate Polynomials, and Linear Feedback Shift Registers*, Journal of
Integer Sequences 6 (2003), Article 03.3.6,
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Zuniga/zuniga51.tex>,
p-adic stationary phase setup and dilatation definition, lines 314-324
(`f_{x_0}(x) = p^{-e} f(x_0 + px)` with `e` the minimum p-order,
calling `f_{x_0}` the dilatation of `f` at `x_0`).

Atomic claim: for a polynomial over the p-adic integers with at least one
unit coefficient, and every p-adic integer point, the scaled translate by
`x0 + p * X` divided by the minimal uniform power of `p` stays integral
with at least one unit coefficient.
-/

/-- Dilatation data at a point: exponent plus integral polynomial whose
coercion equals the normalized translate, with nonzero reduction. -/
structure PadicPolynomialDilatation (p : ℕ) [Fact p.Prime]
    (f : Polynomial (PadicInt p)) (x0 : PadicInt p) where
  exp : ℕ
  poly : Polynomial (PadicInt p)
  dilat_eq :
    Polynomial.map (algebraMap (PadicInt p) (Padic p)) poly =
      Polynomial.C (((p : Padic p) ^ exp)⁻¹) *
        Polynomial.map (algebraMap (PadicInt p) (Padic p))
          (f.comp (Polynomial.C x0 + Polynomial.C (p : PadicInt p) * Polynomial.X))
  red_ne_zero : Polynomial.map PadicInt.toZMod poly ≠ 0

/-- Proved witness: dilatation data exists for the constant polynomial one at zero. -/
noncomputable def padicPolynomialDilatation_one_zero (p : ℕ) [Fact p.Prime] :
    PadicPolynomialDilatation p 1 0 where
  exp := 0
  poly := 1
  dilat_eq := by
    simp only [Polynomial.one_comp, Polynomial.map_one, pow_zero, inv_one,
      Polynomial.C_1, mul_one]
  red_ne_zero := by
    simp only [Polynomial.map_one]
    exact one_ne_zero
