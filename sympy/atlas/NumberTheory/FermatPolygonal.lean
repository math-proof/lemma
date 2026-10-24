/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatPolygonal.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import sympy.atlas.NumberTheory.PolygonalNumber
import Lemma.Nat.PolygonalNumber
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic
import Lemma.Nat.QuadraticForms.LegendreThreeSquare
/-!
# Fermat's polygonal number theorem

This file proves Gauss's three-triangular-number theorem, Cauchy's four-square
lemma with a prescribed sum, and Fermat's theorem that every natural number is
a sum of at most `s` nonnegative `s`-gonal numbers.

Wikipedia states the theorem for positive integers; the Lean statement also covers `n = 0`
(the empty sum, and `Nat.polygonalNumber s 0 = 0`).

## References

* A.-L. Cauchy, *Démonstration du théorème général de Fermat sur les nombres polygones*,
  Mém. Sci. Math. Phys. Inst. France (1) 14 (1813-15), 177-220 = *Oeuvres* (2) vol. 6, 320-353.
* M. B. Nathanson, *A short proof of Cauchy's polygonal number theorem*,
  Proc. Amer. Math. Soc. 99 (1987), 22-24.
* M. B. Nathanson, *Additive Number Theory: The Classical Bases*, GTM 164, Springer (1996),
  Ch. 1.
* *Fermat polygonal number theorem*, Wikipedia,
  <https://en.wikipedia.org/wiki/Fermat_polygonal_number_theorem>.
-/

open scoped BigOperators

namespace Nat

end Nat
namespace MetaMathlibExt
private def fermatPolyRoute (m n : ℕ) : Prop :=
  ∃ d b r : ℕ, b % 2 = 1 ∧ r ≤ m - 2 ∧ n = m * d + b + r ∧
    (b : ℤ) ^ 2 - 4 * b < 8 * d ∧ 6 * (d : ℤ) < b ^ 2 - b + 4

private def fermatPolyRouteAtB (m n b : ℕ) : Bool :=
  let r := (n - b) % m
  let d := (n - b) / m
  decide (b ≤ n ∧ r ≤ m - 2 ∧
    (b : ℤ) ^ 2 - 4 * b < 8 * d ∧ 6 * (d : ℤ) < (b : ℤ) ^ 2 - b + 4)

private def fermatPolyRouteB (m n : ℕ) : Bool :=
  (List.range 17).any fun j ↦ fermatPolyRouteAtB m n (2 * j + 1)

private def fermatPolyFamB (m n : ℕ) : Bool :=
  decide (n = m * 2 + 4 ∨ n = m * 3 + 4 ∨ n = m * 4 + 6 ∨
    n = m * 5 + 6 ∨ n = m * 6 + 6 ∨ n = m * 8 + 8 ∨
    n = m * 9 + 8 ∨ n = m * 10 + 8 ∨ n = m * 13 + 10 ∨
    n = m * 14 + 10 ∨ n = m * 15 + 10 ∨ n = m * 19 + 12 ∨
    n = m * 20 + 12 ∨ n = m * 21 + 12 ∨ n = m * 27 + 14 ∨
    n = m * 28 + 14 ∨ n = m * 36 + 16)

private def fermatPolySmallGoodB (m n : ℕ) : Bool :=
  fermatPolyRouteB m n || fermatPolyFamB m n || decide (n ≤ m + 2)

private def fermatPolyRoutePairAtB (q rho b : ℕ) : Bool :=
  decide ((b ≤ rho ∧ (b : ℤ) ^ 2 - 4 * b < 8 * (q : ℤ) ∧
      6 * (q : ℤ) < (b : ℤ) ^ 2 - b + 4) ∨
    (rho + 2 ≤ b ∧ 1 ≤ q ∧
      (b : ℤ) ^ 2 - 4 * b < 8 * ((q - 1 : ℕ) : ℤ) ∧
      6 * ((q - 1 : ℕ) : ℤ) < (b : ℤ) ^ 2 - b + 4))

private def fermatPolyRoutePairB (q rho : ℕ) : Bool :=
  (List.range 17).any fun j ↦ fermatPolyRoutePairAtB q rho (2 * j + 1)

private def fermatPolyFamPairB (q rho : ℕ) : Bool :=
  decide ((q = 2 ∧ rho = 4) ∨ (q = 3 ∧ rho = 4) ∨ (q = 4 ∧ rho = 6) ∨
    (q = 5 ∧ rho = 6) ∨ (q = 6 ∧ rho = 6) ∨ (q = 8 ∧ rho = 8) ∨
    (q = 9 ∧ rho = 8) ∨ (q = 10 ∧ rho = 8) ∨ (q = 13 ∧ rho = 10) ∨
    (q = 14 ∧ rho = 10) ∨ (q = 15 ∧ rho = 10) ∨ (q = 19 ∧ rho = 12) ∨
    (q = 20 ∧ rho = 12) ∨ (q = 21 ∧ rho = 12) ∨ (q = 27 ∧ rho = 14) ∨
    (q = 28 ∧ rho = 14) ∨ (q = 36 ∧ rho = 16))

private def fermatPolyPairGoodB (q rho : ℕ) : Bool :=
  fermatPolyRoutePairB q rho || fermatPolyFamPairB q rho ||
    decide (q = 0 ∨ (q = 1 ∧ rho ≤ 2))
end MetaMathlibExt
