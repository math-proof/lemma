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
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec17AbelJacobi.Part2
set_option maxHeartbeats 800000


noncomputable section

namespace Lec17AbelJacobi

open AlgebraicGeometry CategoryTheory

/-- Two period lattice data are equivalent if there is a `ℂ`-linear isomorphism between
the ambient spaces carrying one lattice onto the other. -/
def PeriodLatticeData.Equivalent (D₁ D₂ : PeriodLatticeData) : Prop :=
  ∃ (φ : (Fin D₁.genus → ℂ) ≃ₗ[ℂ] (Fin D₂.genus → ℂ)),
    ∀ v : Fin D₁.genus → ℂ, v ∈ D₁.lattice ↔ φ v ∈ D₂.lattice

/-- Two smooth compact complex curves are isomorphic over `ℂ` if there is an
isomorphism of schemes compatible with their structure morphisms to `Spec ℂ`. -/
def SmoothCompactComplexCurve.IsIsomorphicOver (X₁ X₂ : SmoothCompactComplexCurve) : Prop :=
  ∃ (f : X₁.toScheme ⟶ X₂.toScheme), IsIso f ∧
    X₁.structureMorphism = f ≫ X₂.structureMorphism

end Lec17AbelJacobi
end
