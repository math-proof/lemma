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
public import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part4
open scoped LinearAlgebra.Projectivization


@[expose] public noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveVarietyDef

variable {n : ℕ} (k : Type*) [Field k]

/-- Coordinate ring of $V \subseteq \overline{k}^N$: the quotient
$\overline{k}[X_1, \ldots, X_N] / I(V)$. -/
abbrev coordinateRing' (N : ℕ) (V : Set (AffinePoint k N)) :=
  MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ vanishingIdeal' k N V

end ProjectiveVarietyDef
end
