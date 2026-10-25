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
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part4
open scoped LinearAlgebra.Projectivization


noncomputable section

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
