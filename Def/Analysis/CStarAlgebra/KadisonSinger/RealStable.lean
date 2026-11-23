/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Def.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
public import Theorem.Real.CStarAlgebra.KadisonSinger.MixedCharPoly
public import Theorem.MvPolynomial.Stable
public import Def.Algebra.MvPolynomial.Stable
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Data.List.OfFn
public import Mathlib.Topology.MetricSpace.Sequences

@[expose] public section

open scoped BigOperators ComplexOrder

/-!
# Real stable multivariate polynomials

This file develops the real-stability facts used in the Marcus--Spielman--Srivastava proof.
-/


namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

open Filter MvPolynomial

noncomputable def ksPolynomialIn {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (p : MvPolynomial σ R) :
    Polynomial (MvPolynomial {j : σ // j ≠ i} R) :=
  optionEquivLeft R {j : σ // j ≠ i} (rename (Equiv.optionSubtypeNe i).symm p)

def ksMonicIn {σ R : Type*} [CommRing R]
    (i : σ) (d : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∃ q, p = X i ^ d + q ∧ q.degreeOf i < d

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger
