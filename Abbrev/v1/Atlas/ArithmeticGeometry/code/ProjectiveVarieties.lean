/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing


noncomputable section

open MvPolynomial Finsupp

namespace HomogeneousPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- A multivariate polynomial $f$ is homogeneous of degree $d$ if every monomial
in $f$ has total degree $d$. Abbreviation for Mathlib's `MvPolynomial.IsHomogeneous`. -/
abbrev IsHomogeneousOfDegree (f : MvPolynomial σ R) (d : ℕ) : Prop :=
  f.IsHomogeneous d

end HomogeneousPolynomial
end
