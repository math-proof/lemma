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
set_option maxHeartbeats 800000


noncomputable section

namespace Lec17AbelJacobi

open AlgebraicGeometry CategoryTheory

/-- The scheme `Spec ℂ`, used as the base in the smooth-complex-curve setup of Lec 17. -/
def SpecC : Scheme := Scheme.Spec.obj (Opposite.op (CommRingCat.of ℂ))

end Lec17AbelJacobi
end
