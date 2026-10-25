/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/FourTriangularNumbers.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Order.Interval.Finset.Nat


namespace MetaMathlibExt.FourTriangular

/-- Triangular numbers `T(u) = u * (u + 1) / 2`, spelled as in the Wanted statement. -/
def ftnTri (u : ℕ) : ℕ := u * (u + 1) / 2

/-- `t2(a)`: number of pairs `(u, v)` with `T(u) + T(v) = a`. -/
def ftnTriPairCount (a : ℕ) : ℕ :=
  ((Finset.range (a + 1) ×ˢ Finset.range (a + 1)).filter
    (fun p => ftnTri p.1 + ftnTri p.2 = a)).card

/-- `S(N)`: Gaussian integers of norm `N`. Its count is `g(N)`. -/
def ftnGaussNormSet (N : ℕ) : Set GaussianInt := { z | z.norm = (N : ℤ) }

/-- `Reg(N)`: Gaussian integers of norm `N` with `|im| < re`. -/
def ftnGaussNormRegion (N : ℕ) : Set GaussianInt :=
  { z | |z.im| < z.re ∧ z.norm = (N : ℤ) }

/-- `h(N) = ∑_{d | N} χ₄(d)`, valued in `ℤ`. -/
noncomputable def ftnChiFourDivisorSum (N : ℕ) : ℤ :=
  ∑ d ∈ N.divisors, ZMod.χ₄ (d : ZMod 4)

/-- `Quad(N)`: quadruples `(a, x, b, y)` of positive naturals with
`a * x + b * y = N`, `x` odd, `y` odd. -/
def ftnOddQuad (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)))).filter
    (fun q => q.1 * q.2.1 + q.2.2.1 * q.2.2.2 = N ∧ Odd q.2.1 ∧ Odd q.2.2.2)

/-- `V(N)`: quadruples `(c, X, b, Y)` of positive naturals with
`c * X + b * Y = N`, `X` odd, `Y` even. -/
def ftnLiouvilleTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)))).filter
    (fun q => q.1 * q.2.1 + q.2.2.1 * q.2.2.2 = N ∧ Odd q.2.1 ∧ Even q.2.2.2)

def ftnGaussNormRegion1 (N : ℕ) : Set GaussianInt :=
  { z | |z.re| < z.im ∧ z.norm = (N : ℤ) }

def ftnGaussNormRegion2 (N : ℕ) : Set GaussianInt :=
  { z | |z.im| < -z.re ∧ z.norm = (N : ℤ) }

def ftnGaussNormRegion3 (N : ℕ) : Set GaussianInt :=
  { z | |z.re| < -z.im ∧ z.norm = (N : ℤ) }

/-- χ₄ as an `ArithmeticFunction ℤ`. -/
def ftnChiFour : ArithmeticFunction ℤ :=
  ⟨fun n => ZMod.χ₄ ((n : ℕ) : ZMod 4), by decide⟩

def ftnFourInd (k : ℤ) : ℤ := if (4 : ℤ) ∣ k then 1 else 0

end MetaMathlibExt.FourTriangular
