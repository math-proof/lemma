/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Structure.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology

@[expose] public section

open groupCohomology


namespace GaloisCohomology

namespace CrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A `CrossedHom G A` can be coerced to a function $G \to A$ in a `FunLike` manner. -/
instance : FunLike (CrossedHom G A) G A where
  coe := CrossedHom.toFun
  coe_injective f g h := by cases f; cases g; congr

end CrossedHom
end GaloisCohomology
