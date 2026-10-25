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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec17AbelJacobi.Part3
set_option maxHeartbeats 800000


noncomputable section

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
