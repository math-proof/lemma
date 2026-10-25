/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
import Lemma.Real.CStarAlgebra.KadisonSinger.MixedCharPoly
import Lemma.MvPolynomial.Stable
import Def.Algebra.MvPolynomial.Stable
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.List.OfFn
import Mathlib.Topology.MetricSpace.Sequences
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
