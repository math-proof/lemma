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
import Def.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology
open groupCohomology


namespace GaloisCohomology

/-- A bundled crossed homomorphism: a function $G \to A$ together with a proof of the cocycle
condition. -/
structure CrossedHom (G A : Type*) [Mul G] [AddCommGroup A] [SMul G A] where
  toFun : G → A
  cocycle_condition : IsCrossedHom toFun

end GaloisCohomology
