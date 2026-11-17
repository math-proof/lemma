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
public import Def.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology
public section

open groupCohomology


namespace GaloisCohomology

/-- A bundled crossed homomorphism: a function $G \to A$ together with a proof of the cocycle
condition. -/
structure CrossedHom (G A : Type*) [Mul G] [AddCommGroup A] [SMul G A] where
  toFun : G → A
  cocycle_condition : IsCrossedHom toFun

end GaloisCohomology
