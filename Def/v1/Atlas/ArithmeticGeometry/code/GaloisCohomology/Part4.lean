module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Instance.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part6
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

/-- A function $\alpha \colon G \to A$ is a *principal crossed homomorphism* (1-coboundary) iff it
has the form $\alpha(\sigma) = \sigma \cdot P - P$ for some $P \in A$. -/
def IsPrincipalCrossedHom (α : G → A) : Prop :=
  groupCohomology.IsCoboundary₁ α

end PrincipalCrossedHom
