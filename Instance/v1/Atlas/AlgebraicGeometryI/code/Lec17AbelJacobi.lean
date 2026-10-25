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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec17AbelJacobi.Part4
set_option maxHeartbeats 800000


noncomputable section

namespace Lec17AbelJacobi

open AlgebraicGeometry CategoryTheory

attribute [instance] IrreducibleCompleteCurve.instCommRing
  IrreducibleCompleteCurve.instIsDomain IrreducibleCompleteCurve.instIsDedekind

/-- `Pic⁰(X)` inherits a commutative group structure from the class group. -/
instance instCommGroupPic0Group {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : CommGroup X.Pic0Group := by
  unfold IrreducibleCompleteCurve.Pic0Group; infer_instance

/-- Normalization factorization: any non-constant morphism `f : X → Y` factors as a
birational map `X → NorY` followed by a finite normalization `NorY → Y`, with both `X`
and `NorY` normal. -/
instance elliptic_curve_addCommGroup
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    AddCommGroup W.Point :=
  inferInstance

end Lec17AbelJacobi
end
