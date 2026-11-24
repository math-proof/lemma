module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Def.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part7
open groupCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The group structure on $E(\bar k)$ coming from the Weierstrass curve's affine point group law. -/
noncomputable instance instAddCommGroupECurvePointsAlgClosure (k : Type*) [Field k]
    (W : WeierstrassCurve k) :
    AddCommGroup (ECurvePointsAlgClosure k W) :=
  WeierstrassCurve.Affine.Point.instAddCommGroup (F := AlgebraicClosure k)

end PrincipalCrossedHom
