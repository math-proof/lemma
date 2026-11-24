module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Def.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part2
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

/-- The zero element of `CrossedHom G A`. -/
instance : Zero (CrossedHom G A) := ⟨zero⟩

/-- Pointwise addition on `CrossedHom G A`. -/
instance : Add (CrossedHom G A) := ⟨add⟩

/-- Pointwise negation on `CrossedHom G A`. -/
instance : Neg (CrossedHom G A) := ⟨neg⟩

end CrossedHom
end GaloisCohomology
