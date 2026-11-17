/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Theorem.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties


@[expose] public noncomputable section

open MvPolynomial Finsupp

namespace HomogeneousPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- An ideal $I \subseteq R[X_1, \ldots, X_n]$ is homogeneous if every $f \in I$
has all of its homogeneous components in $I$. -/
abbrev IsHomogeneousIdeal (I : Ideal (MvPolynomial σ R)) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ R)


end HomogeneousPolynomial
end
