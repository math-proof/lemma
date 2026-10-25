/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PolynomialReciprocalStructural.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SmoothingOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.QuotientFDerivStep
import Def.v1.Atlas.DifferentialAnalysis.code.QuotientFDerivStep
open MvPolynomial Finsupp


noncomputable section

namespace DifferentialOperators

variable {σ : Type*} {R : Type*} [CommRing R]

/-- Iterated partial derivative of a complex-valued function on `ℝⁿ` along the list of coordinate
directions `js`, applied left-to-right via `List.foldl`. -/
def iteratedPartialDeriv (js : List (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℂ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  js.foldl (fun g j => fun ξ => fderiv ℝ g ξ (EuclideanSpace.single j 1)) f

/-- Recursive definition of the numerator polynomial obtained when differentiating `1 / P` along
the list of directions `js`; see Lemma 11.14 of Melrose for the resulting structural identity. -/
def reciprocalNumerator (P : MvPolynomial (Fin n) ℂ) :
    List (Fin n) → MvPolynomial (Fin n) ℂ
  | [] => 1
  | j :: rest =>
    let L := reciprocalNumerator P rest
    P * pderiv j L - (1 + rest.length : ℕ) • (L * pderiv j P)

/-- Left-fold version of the reciprocal numerator construction, threading a running numerator `Q`
and a running power index `k` along the list of differentiation directions. -/
def foldNumerator (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ → ℕ → List (Fin n) → MvPolynomial (Fin n) ℂ
  | Q, _, [] => Q
  | Q, k, j :: rest => foldNumerator P (P * pderiv j Q - k • (Q * pderiv j P)) (k + 1) rest

end DifferentialOperators
end
