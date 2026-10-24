/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/AbelBernoulliSums.lean -/

import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal

namespace MetaMathlibExt

open Finset Nat Polynomial

/-- Finite-difference sum: S(m,j,x) = ∑_{l=0}^m C(m,l) (-1)^{m-l} (x+l)^j. -/
private noncomputable def S (m j : ℕ) (x : ℂ) : ℂ :=
  ∑ l ∈ Finset.range (m + 1), (Nat.choose m l : ℂ) * (-1 : ℂ) ^ (m - l) * (x + (l : ℂ)) ^ j

/-- Auxiliary summand for the reindexed sum. -/
private noncomputable def g (m j : ℕ) (x : ℂ) : ℕ → ℂ :=
  fun k => (Nat.choose m k : ℂ) * (-1 : ℂ) ^ (m + 1 - k) * (x + (k : ℂ)) ^ j

/-- Abel summand factor: x * (x + l)^{l-1}, via zpow to include l = 0. -/
private noncomputable def abelCoeff (x : ℂ) (l : ℕ) : ℂ := x * (x + (l : ℂ)) ^ ((l : ℤ) - 1)

/-- The Abel sum as a polynomial in the second argument. -/
private noncomputable def AbelPoly (x : ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ l ∈ Finset.range (m + 1),
    Polynomial.C ((Nat.choose m l : ℂ) * abelCoeff x l) *
      (Polynomial.X - Polynomial.C (l : ℂ)) ^ (m - l)
end MetaMathlibExt
