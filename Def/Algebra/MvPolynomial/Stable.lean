/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.Algebra.Polynomial.RealRooted.Part2
import Lemma.Polynomial.RealRooted
import Lemma.MvPolynomial.PDeriv
import Def.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.List.OfFn
import Mathlib.Topology.MetricSpace.Sequences
open scoped BigOperators ComplexOrder


namespace MvPolynomial

/-- A complex multivariate polynomial is stable if it has no zero when every variable lies in the
open upper half-plane. -/
def IsStable {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, 0 < (z i).im) → eval z p ≠ 0

/-- A complex multivariate polynomial is real stable if it is stable and has real coefficients. -/
def IsRealStable {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  map (starRingEnd ℂ) p = p ∧ p.IsStable

/-- Regard one variable of a multivariate polynomial as the variable of a univariate polynomial,
and specialize all other variables. -/
noncomputable def univariateSpecialization {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (x : σ → R) (p : MvPolynomial σ R) : Polynomial R :=
  eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j)) p

end MvPolynomial

namespace MathlibExt.Algebra.MvPolynomialStable

noncomputable def ksPolynomialIn {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (p : MvPolynomial σ R) :
    Polynomial (MvPolynomial {j : σ // j ≠ i} R) :=
  optionEquivLeft R {j : σ // j ≠ i} (rename (Equiv.optionSubtypeNe i).symm p)

end MathlibExt.Algebra.MvPolynomialStable
