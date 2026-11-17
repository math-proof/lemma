/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AbelJacobi.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.ClassGroup
set_option maxHeartbeats 400000

public section

/-- Abel-Jacobi surjectivity: every divisor class in `Pic⁰(W)` is represented by a point of the
elliptic curve `W`. Together with injectivity this gives the bijection `W ≅ Pic⁰(W)` (Thm 17.2,
Lec 17). -/


namespace AbelJacobi

open WeierstrassCurve.Affine

end AbelJacobi
