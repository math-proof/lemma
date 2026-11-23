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
public import Instance.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology
open groupCohomology

public section

namespace GaloisCohomology

namespace CrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- Crossed homomorphisms are determined by their function values: two crossed homs agreeing
pointwise are equal. -/
@[ext]
theorem ext {α β : CrossedHom G A} (h : ∀ g, α g = β g) : α = β :=
  DFunLike.ext α β h

end CrossedHom
end GaloisCohomology
