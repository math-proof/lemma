/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec17AbelJacobi.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec17AbelJacobi
set_option maxHeartbeats 800000


noncomputable section

namespace Lec17AbelJacobi

open AlgebraicGeometry CategoryTheory

/-- Converts a complex period lattice into the Weierstrass cubic
`y² = 4x³ - g₂(L) x - g₃(L)`, with `aᵢ` coefficients adjusted to standard short form. -/
def periodPairToWeierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(L.g₂ / 4)
  a₆ := -(L.g₃ / 4)

/-- Two period pairs are homothetic if their lattices are scalar multiples of each
other by some nonzero complex `α`. -/
def LatticePairHomothetic (L₁ L₂ : PeriodPair) : Prop :=
  ∃ α : ℂ, α ≠ 0 ∧
    (∀ z : ℂ, z ∈ L₁.lattice ↔ ∃ w ∈ L₂.lattice, z = α * w)

end Lec17AbelJacobi
end
