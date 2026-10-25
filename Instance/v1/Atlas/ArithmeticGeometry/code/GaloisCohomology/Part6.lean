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
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part4
open groupCohomology


namespace ContCrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]
    [TopologicalSpace G] [TopologicalSpace A]

/-- Continuous crossed homomorphisms form an additive commutative group. -/
instance : AddCommGroup (ContCrossedHom G A) where
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

end ContCrossedHom
