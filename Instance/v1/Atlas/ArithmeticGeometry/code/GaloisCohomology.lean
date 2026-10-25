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
import Structure.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology
open groupCohomology


namespace GaloisCohomology

namespace CrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A `CrossedHom G A` can be coerced to a function $G \to A$ in a `FunLike` manner. -/
instance : FunLike (CrossedHom G A) G A where
  coe := CrossedHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

end CrossedHom
end GaloisCohomology
