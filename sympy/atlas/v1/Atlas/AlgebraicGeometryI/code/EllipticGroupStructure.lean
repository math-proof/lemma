/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticGroupStructure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.ClassGroup

set_option maxHeartbeats 400000

open WeierstrassCurve.Affine in
/-- The set of points on an affine elliptic curve forms an abelian group under
the chord-tangent law: this is the analytic / classical group law on `E(F)`. -/
instance elliptic_curve_group_structure {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    AddCommGroup W.Point := inferInstance

open WeierstrassCurve.Affine in
/-- The Abel-Jacobi map `Point.toClass` from points on the elliptic curve to
the class group of the coordinate ring is surjective: every divisor class is
represented by a point (Cor 21, Lec 14/15). -/
