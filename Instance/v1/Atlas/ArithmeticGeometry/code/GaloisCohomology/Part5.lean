module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Def.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part3
open groupCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ContCrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]
    [TopologicalSpace G] [TopologicalSpace A]

/-- Zero on `ContCrossedHom`. -/
instance : Zero (ContCrossedHom G A) := ⟨zero⟩

/-- Pointwise addition on `ContCrossedHom`. -/
instance : Add (ContCrossedHom G A) := ⟨add⟩

/-- Pointwise negation on `ContCrossedHom`. -/
instance : Neg (ContCrossedHom G A) := ⟨neg⟩

end ContCrossedHom
