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
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec17AbelJacobi.Part3
set_option maxHeartbeats 800000


public noncomputable section

namespace Lec17AbelJacobi

open AlgebraicGeometry CategoryTheory

/-- Assigns to a smooth compact complex curve its period lattice in `ℂ^{genus}`. -/
structure AbelianGroupScheme where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isProper : IsProper structureMorphism
  isSmooth : Smooth structureMorphism
  identitySection : SpecC ⟶ toScheme
  identitySection_comp : identitySection ≫ structureMorphism = 𝟙 SpecC

/-- Proposition 26 (Lec 17): existence of the Jacobian variety and the Abel–Jacobi map
`X → Jac(X)` over `ℂ`, compatible with structure morphisms to `Spec ℂ`. -/
structure IrreducibleCompleteCurve (k : Type*) [Field k] : Type 1 where
  coordinateRing : Type
  [instCommRing : CommRing coordinateRing]
  [instIsDomain : IsDomain coordinateRing]
  [instIsDedekind : IsDedekindDomain coordinateRing]

attribute [instance] IrreducibleCompleteCurve.instCommRing
  IrreducibleCompleteCurve.instIsDomain IrreducibleCompleteCurve.instIsDedekind

/-- A morphism `X → Y` of irreducible complete curves, contravariantly described by a
ring homomorphism on coordinate rings `Y.coordinateRing → X.coordinateRing`. -/
structure CurveMorphism {k : Type*} [Field k]
    (X Y : IrreducibleCompleteCurve k) : Type where
  ringHom : Y.coordinateRing →+* X.coordinateRing

end Lec17AbelJacobi
end
