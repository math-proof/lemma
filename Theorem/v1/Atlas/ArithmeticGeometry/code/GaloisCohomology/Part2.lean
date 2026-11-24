module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Instance.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part2
open groupCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace GaloisCohomology

namespace CrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- The zero crossed hom evaluates to $0$ at every $g \in G$. -/
@[simp] theorem zero_apply (g : G) : (0 : CrossedHom G A) g = 0 := rfl

/-- Sum of two crossed homs evaluates pointwise. -/
@[simp] theorem add_apply (α β : CrossedHom G A) (g : G) : (α + β) g = α g + β g := rfl

/-- Negation of a crossed hom evaluates pointwise. -/
@[simp] theorem neg_apply (α : CrossedHom G A) (g : G) : (-α) g = -(α g) := rfl

end CrossedHom
end GaloisCohomology
