/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec17AbelJacobi.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec17AbelJacobi.Part2

@[expose] public section

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
