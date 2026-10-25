/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.MulAction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.SeparableClosure
open groupCohomology


namespace GaloisCohomology

/-- A function $\alpha \colon G \to A$ is a *crossed homomorphism* (1-cocycle) iff it satisfies the
cocycle identity $\alpha(\tau\sigma) = \alpha(\tau) + \tau \cdot \alpha(\sigma)$, identified here
with `groupCohomology.IsCocycle₁`. -/
def IsCrossedHom {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A] (α : G → A) : Prop :=
  groupCohomology.IsCocycle₁ α

end GaloisCohomology
