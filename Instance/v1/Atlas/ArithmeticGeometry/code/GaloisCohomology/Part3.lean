module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part2
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

/-- Crossed homomorphisms form an additive commutative group under pointwise operations. -/
instance : AddCommGroup (CrossedHom G A) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc α β γ := by ext g; simp [add_assoc]
  zero_add α := by ext g; simp
  add_zero α := by ext g; simp
  add_comm α β := by ext g; simp [add_comm]
  neg_add_cancel α := by ext g; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

end CrossedHom
end GaloisCohomology
